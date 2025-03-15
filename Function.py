from typing import List, Dict, Any
from loguru import logger
from slither.core.declarations import (
    Function, 
    Contract, 
    SolidityVariable,
    SolidityFunction,
    Modifier,
) 
from slither.core.cfg.node import NodeType, Node
from slither.core.variables import (
    StateVariable,
    Variable,
    LocalVariable,
)
from slither.slithir.variables import (
    ReferenceVariable,
    TemporaryVariable,
    Constant,
    TupleVariable,
)
from slither.core.solidity_types import (
    ElementaryType,
    MappingType,
)
from slither.slithir.operations import(
    Operation,
    Member,
    Binary,
    Call,
    InternalCall,
    HighLevelCall,
    Return,
    SolidityCall,
    BinaryType,
    Index,
    Assignment,
    TypeConversion,
    Unary,
    UnaryType,
    Unpack,
    LibraryCall,
    Condition,
)
from z3 import *
from FFormula import FFormula, FStateVar, ExpressionWithConstraint, Reconstruct_If
from FType import FMap, FTuple, BINARY_OP
from FFuncContext import FFuncContext 
import config


class FFunction:
    def __init__(self, func:Function, parentContract):
        from Contract import FContract
        self.func = func
        self.parent_contract:FContract = parentContract
        # all state variables written in this function
        self.stateVarWrite = self.func.state_variables_written
        self.highlevelCalls = self.func.all_high_level_calls
        self.FormulaMap:Dict[FStateVar, FFormula] = {}
        self.WaitCall = False
        self.solver = Solver()

    
    def Check_constraint(self, cons:ExprRef) -> bool:
        self.solver.push()
        self.solver.add(cons)
        res = self.solver.check()
        self.solver.pop()
        return res == sat
    

    def Implied_exp(self, expr1, expr2):
        if config.refined:
            self.solver.push()
            self.solver.add(And(expr1, Not(expr2)))
            res_1 = self.solver.check() == unsat
            self.solver.pop()
            self.solver.push()
            self.solver.add(And(expr2, Not(expr1)))
            res_2 = self.solver.check() == unsat
            self.solver.pop()
            if res_1:
                return expr1
            elif res_2:
                return expr2
            else:
                return And(expr1, expr2)
        else:
            return And(expr1, expr2)

    
    def addFFormula(self, stateVar:FStateVar, fformula:FFormula=None, context:FFuncContext=None, repeat:bool=False):
        if stateVar in self.FormulaMap:
            if repeat:
                for exp, cons in fformula.expressions_with_constraints:
                    self.FormulaMap[stateVar].expressions_with_constraints.append(ExpressionWithConstraint(exp, simplify(self.Implied_exp(context.globalFuncConstraint, cons))))
                    # delete redundant expressions
                    self.FormulaMap[stateVar].expressions_with_constraints = list(set(self.FormulaMap[stateVar].expressions_with_constraints))
            else:
                self.FormulaMap[stateVar].expressions_with_constraints.extend(fformula.expressions_with_constraints)
        else:
            if repeat:
                self.FormulaMap[stateVar] = FFormula(stateVar, fformula.parent_contract, fformula.parent_function)
                for exp, cons in fformula.expressions_with_constraints:
                    self.FormulaMap[stateVar].expressions_with_constraints.append(ExpressionWithConstraint(exp, simplify(self.Implied_exp(context.globalFuncConstraint, cons))))
                # delete redundant expressions
                self.FormulaMap[stateVar].expressions_with_constraints = list(set(self.FormulaMap[stateVar].expressions_with_constraints))
            else:
                self.FormulaMap[stateVar] = fformula


    def printFFormulaMap(self):
        for stateVar, fformula in self.FormulaMap.items():
            if len(fformula.expressions_with_constraints) == 0:
                continue
            logger.debug(f"StateVar: {stateVar.stateVar.name} in function {self.func.canonical_name}, formula: {fformula}")


    def __str__(self):
        return f"Function: [{self.func.name}] in contract [{self.parent_contract.main_name}]"


    def analyzeNode(self, node: Node, context:FFuncContext):
        # del formula map of temp variable
        context.clearTempVariableCache()
        if node.type in {NodeType.EXPRESSION, NodeType.VARIABLE, NodeType.RETURN}:
            self.analyzeNodeIRs(node, context)

        # modifier call, just stop when meets '_'
        elif node.type == NodeType.PLACEHOLDER:
            pass

        # condition & loop:
        elif node.type == NodeType.IF:
            self.analyzeNodeIRs(node, context)

        elif node.type == NodeType.ENDIF:
            pass

        elif node.type == NodeType.STARTLOOP:
            pass
        
        # true -> loop body | false -> end loop(node)
        elif node.type == NodeType.IFLOOP:
            context.loop_count[node] += 1
            self.analyzeNodeIRs(node, context)

        elif node.type == NodeType.ENDLOOP:
            pass

        # callee function's modification on state variables will be handled when it returns
        if self.is_terminal_node(node) and not context.stop:
            if not self.WaitCall and not context.parent_func:
                for var, formula in context.currentFormulaMap.items():
                    if len(formula.expressions_with_constraints) == 0:
                        continue
                    if isinstance(var, StateVariable) or (isinstance(var, FMap) and isinstance(var.map, StateVariable)):
                        self.addFFormula(FStateVar(self.parent_contract, var), formula, context, repeat=True)
            else:
                for var, formula in context.currentFormulaMap.items():
                    if len(formula.expressions_with_constraints) == 0:
                        continue
                    context.mergeFormula(var, formula)         
        return
    
    
    def is_terminal_node(self, node:Node) -> bool:
        if node.type in {NodeType.THROW}:
            return False
        if not node.sons or node.type == NodeType.RETURN or node.type == NodeType.PLACEHOLDER:
            return True
        return False
    

    def analyzeNodeIRs(self, node:Node, context:FFuncContext):
        for ir in node.irs:
            if context.stop:
                break
            if context.callflag:
                context.returnIRs.append(ir)
            else:
                self.analyzeIR(ir, context)


    def analyzeIR(self, ir:Operation, context:FFuncContext):
        # case by case, no other better way I think
        if isinstance(ir, Binary):
            self.handleBinaryIROp(ir, context)

        elif isinstance(ir, Assignment):
            self.handleAssignmentIR(ir, context)
            
        # convert (this) to address
        elif isinstance(ir, TypeConversion):
            self.handleTypeConversionIR(ir, context)

        # especially handle map/array variable
        elif isinstance(ir, Index):
            self.handleIndexIR(ir, context)

        elif isinstance(ir, Member):
            self.handleMemberIR(ir, context)

        elif isinstance(ir, Unary):
            self.handleUnaryIR(ir, context)

        elif isinstance(ir, Call):
            self.handleCallIR(ir, context)

        elif isinstance(ir, Return):
            self.handleRetIR(ir, context)

        elif isinstance(ir, Unpack):
            self.handleUnpackIR(ir, context)

        elif isinstance(ir, Condition):
            self.handleConditionIR(ir, context)


    def handleConditionIR(self, ir:Condition, context:FFuncContext):
        cond = self.getRefPointsTo(ir.value, context)
        cond_expr = self.handleVariableExpr(cond, context)
        cond_expr_if = Reconstruct_If(cond_expr)
        context.cond_expr_if = simplify(cond_expr_if)
        

    def handleUnpackIR(self, ir:Unpack, context:FFuncContext):
        lvalue = self.getRefPointsTo(ir.lvalue, context)
        tuple_var = FTuple(ir.tuple, ir.index, ir.tuple.type[ir.index])
        rexp = self.handleVariableExpr(tuple_var, context)
        context.currentFormulaMap[lvalue].expressions_with_constraints = rexp
        return
    

    def handleRetIR(self, ir:Return, context:FFuncContext):
        values, l_var = ir.values, len(ir.values)
        assert l_var > 0
        for idx, var in enumerate(values):
            ret_idx = f"ret_{idx}"
            var = self.getRefPointsTo(var, context)
            var_exp = self.handleVariableExpr(var, context)
            context.retVarMap[ret_idx] = FFormula(FStateVar(self.parent_contract, var), self.parent_contract, self)
            if var_exp not in context.retVarMap[ret_idx].expressions_with_constraints:
                context.retVarMap[ret_idx].expressions_with_constraints.extend(var_exp)
        return
    

    # TODO: modifier call
    def handleCallIR(self, ir:Call, context:FFuncContext):
        # tackle with different kinds of call

        # especially for require
        if isinstance(ir, SolidityCall):
            
            if ir.function in [
            SolidityFunction("require(bool,string)"), 
            SolidityFunction("require(bool)"),
            SolidityFunction("require(bool,error)"),
            SolidityFunction("assert(bool)")
            ]: 
                bool_var = ir.arguments[0]
                assert bool_var in context.currentFormulaMap.keys()
                temp_res_set = set()
                for exp in context.currentFormulaMap[bool_var].expressions_with_constraints:
                    temp_res = simplify(And(And(exp.expression, exp.constraint), context.globalFuncConstraint))
                    if not self.Check_constraint(temp_res):
                        continue
                    temp_res_set.add(temp_res)    
                # context.globalFuncConstraint = simplify(Reconstruct_If(temp_res_list) if len(temp_res_list)!=0 else BoolVal(False))
                if len(temp_res_set) == 0:
                    context.globalFuncConstraint = BoolVal(False)
                elif len(temp_res_set) == 1:
                    context.globalFuncConstraint = temp_res_set.pop()
                else:
                    context.globalFuncConstraint = simplify(Or(*temp_res_set))
                # if globalFuncConstraint is still false(can be infer directly), discard the following nodes
                if not self.Check_constraint(context.globalFuncConstraint):
                    context.stop = True
                    return
                
            elif ir.function in [
                SolidityFunction("revert()"),
                SolidityFunction("revert(string)"),
            ]:
                context.stop = True
                return
            
        elif isinstance(ir, InternalCall) or isinstance(ir, HighLevelCall):
            # if ir.is_modifier_call:
            #     continue
            # highlevel call requires more processing
            if isinstance(ir, HighLevelCall):
                pass
            callee_func = FFunction(ir.function, self.parent_contract)
            callee_context = FFuncContext(func=ir.function, parent_contract=self.parent_contract, parent_func=context.func, caller_node=ir.node)
            # shoud AND if_cond when calling 
            callee_context.globalFuncConstraint = simplify(self.Implied_exp(context.globalFuncConstraint, context.branch_cond))
            if not self.Check_constraint(callee_context.globalFuncConstraint):
                context.stop = True
                return
            # add state variable context
            temp_context = context.copy()
            temp_context.clearRefMap()
            temp_context.clearTempVariableCache()
            callee_context.currentFormulaMap = temp_context.currentFormulaMap
            # map args to params
            self.mapArgsToParams(ir, context, callee_context)
            self.pushCallStack(ir, context, callee_context)
            self.WaitCall = True
            context.callflag = True
            if ir.lvalue:
                context.callerRetVar = self.getRefPointsTo(ir.lvalue, context)


    def pushCallStack(self, ir:Call, context:FFuncContext, callee_context:FFuncContext):
        self.call_stack.append((context, [(callee_context, ir.function.entry_point)]))


    # TODO: constant var mapping
    def mapArgsToParams(self, ir:Call, context:FFuncContext, callee_context:FFuncContext):
        for arg, param in zip(ir.arguments, ir.function.parameters):
            arg = self.getRefPointsTo(arg, context)
            logger.debug(f"[CALL] arg: {arg}, param: {param}")
            callee_context.mapIndex2Var[param] = context.mapIndex2Var[arg] if arg in context.mapIndex2Var.keys() else arg
            arg_exprs = self.handleVariableExpr(arg, context)
            callee_context.currentFormulaMap[param] = FFormula(FStateVar(self.parent_contract, param), self.parent_contract, self)
            callee_context.currentFormulaMap[param].expressions_with_constraints = arg_exprs
        return
    

    def handleUnaryIR(self, ir:Unary, context:FFuncContext):
        assert isinstance(ir.lvalue, TemporaryVariable)
        rvalue = self.getRefPointsTo(ir.rvalue, context)
        uop = ir.type
        rexp = self.handleVariableExpr(rvalue, context)
        try:
            if uop == UnaryType.BANG:
                rexp = [ExpressionWithConstraint(simplify(Not(item.expression)), item.constraint) for item in rexp]
        except Exception as e:
            logger.error(f"Error in handling Unary IR: {e}")
        fformula = FFormula(FStateVar(self.parent_contract, ir.lvalue), self.parent_contract, self)
        fformula.expressions_with_constraints = rexp
        context.updateContext(ir.lvalue, fformula)
        return
    
    
    def handleTypeConversionIR(self, ir:TypeConversion, context:FFuncContext):
        assert isinstance(ir.lvalue, TemporaryVariable)
        rvalue = self.getRefPointsTo(ir.variable, context)
        # conversion here
        if not isinstance(rvalue, SolidityVariable):
            rvalue.type = ir.type
        rexp = self.handleVariableExpr(rvalue, context)
        fformula = FFormula(FStateVar(self.parent_contract, ir.lvalue), self.parent_contract, self)
        fformula.expressions_with_constraints = rexp
        context.updateContext(ir.lvalue, fformula)
        return
    

    def handleAssignmentIR(self, ir:Assignment, context:FFuncContext):
        lvalue, rvalue = self.getRefPointsTo(ir.lvalue, context), self.getRefPointsTo(ir.rvalue, context)
        rexp = self.handleVariableExpr(rvalue, context)
        # directly override
        if lvalue not in context.currentFormulaMap.keys():
            fformula = FFormula(FStateVar(self.parent_contract, lvalue), self.parent_contract, self)
            fformula.expressions_with_constraints = rexp
            context.updateContext(lvalue, fformula)
        else:
            context.currentFormulaMap[lvalue].expressions_with_constraints = rexp
        return
    

    def handleMemberIR(self, ir:Member, context:FFuncContext):
        var, field = ir.variable_left, ir.variable_right
        # logger.debug(f"==== [Member] {var}.{field}")
        ref = ir.lvalue # testStruct.age
        if isinstance(ref, ReferenceVariable):
            member_var = FMap(var, field, ref.type)
            context.refMap[ref] = member_var
            if member_var not in context.currentFormulaMap:
                fformula = FFormula(FStateVar(self.parent_contract, member_var), self.parent_contract, self)
                context.updateContext(member_var, fformula)
        return


    def handleIndexIR(self, ir:Index, context:FFuncContext):
        var, idx = ir.variable_left, ir.variable_right
        # logger.debug(f"==== [Index] {var}[{idx}]")
        if isinstance(var.type, MappingType):
            self.handleMapType(ir, context)
        else:
            ref = ir.lvalue # no need to get points_to, as we can only get _balance when we meet _balance[from]
            if isinstance(ref, ReferenceVariable):
                map_var = FMap(var, idx, ref.type)
                context.refMap[ref] = map_var
                if map_var not in context.currentFormulaMap:
                    fformula = FFormula(FStateVar(self.parent_contract, map_var), self.parent_contract, self)
                    context.updateContext(map_var, fformula)
        return

    
    def handleMapType(self, ir:Index, context:FFuncContext):
        var, idx = ir.variable_left, ir.variable_right
        ref = ir.lvalue
        if isinstance(var.type, MappingType):
            type_from, type_to = var.type.type_from, var.type.type_to
            type2type = {
                ElementaryType("uint256"): IntSort(),
                ElementaryType("bool"): BoolSort(),
                ElementaryType("string"): StringSort(),
                ElementaryType("address"): BitVecSort(160),
            }
            map_from, map_to = type2type.get(type_from, IntSort()), type2type.get(type_to, IntSort())
            
            if var not in context.mapVar2Exp.keys():
                MapExp = Array(f"{var.name}", map_from, map_to)
                context.mapVar2Exp[var] = MapExp
            if idx in context.mapIndex2Var.keys():
                map_var = FMap(var, context.mapIndex2Var[idx], ref.type)
            else:    
                map_var = FMap(var, idx, ref.type)
            if isinstance(ref, ReferenceVariable):
                context.refMap[ref] = map_var
                if map_var not in context.currentFormulaMap:
                    fformula = FFormula(FStateVar(self.parent_contract, map_var), self.parent_contract, self)
                    context.updateContext(map_var, fformula)

            # idx_exp = self.handleVariableExpr(idx, context)
            # for exp, cons in idx_exp:
            #     select_var = Select(context.mapVar2Exp[var], exp)
            #     exp_cons = ExpressionWithConstraint(select_var, simplify(cons))
            #     context.currentFormulaMap[map_var].expressions_with_constraints.append(exp_cons)
            context.currentFormulaMap[map_var].expressions_with_constraints = list(set(context.currentFormulaMap[map_var].expressions_with_constraints))
            return
            

    def handleBinaryIROp(self, ir:Binary, context:FFuncContext):
        result = ir.lvalue
        # only care about state variables that will be recorded on-chain
        result = self.getRefPointsTo(result, context)
        left, right = self.getRefPointsTo(ir.variable_left, context), self.getRefPointsTo(ir.variable_right, context)
        lexp, rexp = self.handleVariableExpr(left, context), self.handleVariableExpr(right, context)
        # handle operation
        merged_exprs = self.mergeExpWithConstraints(lexp, rexp, BINARY_OP[ir.type], context)
        if isinstance(result, StateVariable):
            '''
            I think only in ret expr, it needs to be added(or updated) in FormulaMap, 
            otherwise we only update the func context 
            '''
            # so update here.
            context.currentFormulaMap[result].expressions_with_constraints = merged_exprs
        elif isinstance(result, TemporaryVariable):
            # new instance
            fformula = FFormula(FStateVar(self.parent_contract, result), self.parent_contract, self)
            fformula.expressions_with_constraints = merged_exprs
            context.updateContext(result, fformula)
        # LocalVariables/Function Parameters
        else:
            if result in context.currentFormulaMap:
                context.currentFormulaMap[result].expressions_with_constraints = merged_exprs
            else:
                logger.error(f"no such local/params variable {result.name} in context")
        return
    

    def mergeExpWithConstraints(self, lexp:List[ExpressionWithConstraint], rexp:List[ExpressionWithConstraint], op:Any, context:FFuncContext) -> List[ExpressionWithConstraint]:
        res : List[ExpressionWithConstraint] = []
        
        for litem, ritem in zip(lexp, rexp):
            # all possible binary op
            combined_expr = simplify(op(litem.expression, ritem.expression))
            if combined_expr == None:
                logger.error(f"Error in merging expressions: {litem.expression} and {ritem.expression}")
            combined_constraint = simplify(self.Implied_exp(litem.constraint, ritem.constraint))
            if not self.Check_constraint(combined_constraint):
                continue
            res.append(ExpressionWithConstraint(combined_expr, combined_constraint))
        # constaints are not satisfied, discard this branch
        if len(res) == 0:
            context.stop = True
        return res
    

    def assignSymbolicVal(self, var):
        formula = None

        if var.type == ElementaryType("uint256"):
            formula = Int(var.name)
            self.solver.add(formula >= 0)
        elif var.type == ElementaryType("bool"):
            formula = Bool(var.name)
        elif var.type == ElementaryType("string"):
            formula = String(var.name)
        elif var.type == ElementaryType("address"):
            formula = BitVec(var.name, 160)

        return formula


    # TODO: SolidityVariables are not complete.
    def handleVariableExpr(self, var:Variable, context:FFuncContext) -> List[ExpressionWithConstraint]:
        expressions_with_constraints = []
        combine_if_cons = simplify(And(context.globalFuncConstraint, context.branch_cond))
        if not self.Check_constraint(combine_if_cons):
            context.stop = True
            return expressions_with_constraints
        # handle Constant
        if isinstance(var, Constant):
            # logger.debug(f"==== [V] {var.name}, {var.type}, {var.value}")
            formula = None
            if var.type == ElementaryType("uint256"):
                formula = IntVal(var.value)
            elif var.type == ElementaryType("bool"):
                formula = BoolVal(True) if var.value else BoolVal(False)
            elif var.type == ElementaryType("string"):
                formula = StringVal(var.value)
            elif var.type == ElementaryType("address"):
                formula = BitVecVal(var.value, 160)
            varExpr = ExpressionWithConstraint(formula, context.branch_cond)
            expressions_with_constraints.append(varExpr)
        elif isinstance(var, SolidityVariable):
            if var.name == "this":
                formula = self.parent_contract.address_this
                varExpr = ExpressionWithConstraint(formula, context.branch_cond)
                expressions_with_constraints.append(varExpr)
            else:
                # | msg.sender | msg.value | block.timestamp | block.number | block.coinbase | 
                formula = self.assignSymbolicVal(var)
                varExpr = ExpressionWithConstraint(formula, context.branch_cond)
                expressions_with_constraints.append(varExpr)
        else:
            if var in context.currentFormulaMap:
                expressions_with_constraints = context.currentFormulaMap[var].expressions_with_constraints.copy()    
            else:
                fformula = FFormula(FStateVar(self.parent_contract, var), self.parent_contract, self)
                context.updateContext(var, fformula)
            if len(expressions_with_constraints) == 0:
                # assigning a symbolic value (with its name)
                formula = self.assignSymbolicVal(var)
                varExpr = ExpressionWithConstraint(formula, context.branch_cond)
                expressions_with_constraints.append(varExpr)
            else:
                for exp, cons in context.currentFormulaMap[var].expressions_with_constraints:
                    temp_cons = simplify(self.Implied_exp(cons, combine_if_cons))
                    if not self.Check_constraint(temp_cons):
                        continue
                    expressions_with_constraints.append(ExpressionWithConstraint(exp, simplify(self.Implied_exp(cons, context.branch_cond))))

        return list(set(expressions_with_constraints))
         

    def getRefPointsTo(self, ref:Variable, context:FFuncContext):
        if ref in context.refMap:
            return context.refMap[ref]
        while isinstance(ref, ReferenceVariable):
            ref = ref.points_to
        return ref
    

    # TODO: uncompleted
    def updateContext_FuncRet(self, caller_context:FFuncContext, callee_context:FFuncContext):
        # 0. modifier_call
        # if isinstance(callee_context.func, Modifier):
        # caller_context.globalFuncConstraint = simplify(And(And(caller_context.globalFuncConstraint, callee_context.globalFuncConstraint), callee_context.branch_cond))
        caller_context.globalFuncConstraint = self.Implied_exp(caller_context.globalFuncConstraint, self.Implied_exp(callee_context.globalFuncConstraint, callee_context.branch_cond))
        if not self.Check_constraint(caller_context.globalFuncConstraint):
            caller_context.stop = True
            return True
        # 1. update return values
        callerRetVar = caller_context.callerRetVar
        if isinstance(callerRetVar, TemporaryVariable):
            fformula = FFormula(FStateVar(self.parent_contract, callerRetVar), self.parent_contract, self)
            fformula.expressions_with_constraints = callee_context.retVarMap['ret_0'].expressions_with_constraints.copy()
            caller_context.updateContext(callerRetVar, fformula)
        elif isinstance(callerRetVar, TupleVariable):
            assert len(callee_context.retVarMap.keys()) > 0
            for idx in range(len(callee_context.retVarMap.keys())):
                ret_idx = f"ret_{idx}"
                tuple_var = FTuple(callerRetVar, idx, callerRetVar.type[idx])
                fformula = FFormula(FStateVar(self.parent_contract, tuple_var), self.parent_contract, self)
                fformula.expressions_with_constraints = callee_context.retVarMap[ret_idx].expressions_with_constraints.copy()
                caller_context.updateContext(tuple_var, fformula)

        logger.debug(f"[N] Parent Function: {caller_context.parent_func.canonical_name if caller_context.parent_func else 'None'} \n [N] Current Function <{caller_context.func.canonical_name}> Processing node {caller_context.caller_node}")
        while caller_context.returnIRs:
            ir = caller_context.returnIRs.pop(0)
            logger.debug(f"----- ir[{type(ir)}] : {ir}")
            caller_context.callflag = False
            self.analyzeIR(ir, caller_context)
            if caller_context.callflag:
                return True

        # 2. update state varibles
        for var, formula in callee_context.mergeFormulas.items():
            if len(formula.expressions_with_constraints) == 0:
                continue
            if isinstance(var, StateVariable) or (isinstance(var, FMap) and isinstance(var.map, StateVariable)):
                if isinstance(var, FMap) and var.index in callee_context.mapIndex2Var:
                    var = FMap(var.map, callee_context.mapIndex2Var[var.index], var.type)
                caller_context.currentFormulaMap[var] = formula

        if self.is_terminal_node(callee_context.caller_node):
            for var, formula in caller_context.currentFormulaMap.items():
                if len(formula.expressions_with_constraints) == 0:
                    continue
                if isinstance(var, StateVariable) or (isinstance(var, FMap) and isinstance(var.map, StateVariable)):
                    if isinstance(var, FMap) and var.index in callee_context.mapIndex2Var:
                        var = FMap(var.map, caller_context.mapIndex2Var[var.index], var.type)
                    self.addFFormula(FStateVar(self.parent_contract, var), formula)

        return False
    

    def printNodeInfo(self, context:FFuncContext, node:Node):
        logger.debug(f"[N] Parent Function: {context.parent_func.canonical_name if context.parent_func else 'None'} \n [N] Current Function <{context.func.canonical_name}> Processing node {node} {node.node_id}")
        for ir in node.irs:
            logger.debug(f"----- ir[{type(ir)}] : {ir}") 
    
                          
    # reorder basic blocks(nodes) of function (especially for those have modifiers)
    # pass Context to the son nodes
    def buildCFG(self):
        context = FFuncContext(func=self.func, parent_contract=self.parent_contract.sli_contract)
        context.node_path.append(self.func.entry_point)
        self.call_stack = []
        work_list = [(context, self.func.entry_point)]
        self.call_stack.append((False, work_list))

        while self.call_stack:
            self.WaitCall = False
            # add a current_work_list for inter-function/inter-contract analysis
            caller_context, current_work_list = self.call_stack[-1]
            if len(current_work_list) == 0:
                # pop stack
                self.call_stack.pop()
                # update caller context 
                if caller_context:
                    flag = self.updateContext_FuncRet(caller_context, context)
                    # multi calls in the same Node
                    if flag:
                        continue
                    _, current_work_list = self.call_stack[-1]
                    if context.caller_node.type == NodeType.IF or context.caller_node.type == NodeType.IFLOOP:
                        self.process_if_node(caller_context, context.caller_node, current_work_list)
                    else:
                        self.process_general_node(caller_context, context.caller_node, current_work_list)
                    # need to update
                    context = caller_context
                continue

            context, node = current_work_list.pop(0)
            context.callflag = False
            # print debug info
            self.printNodeInfo(context, node)

            self.analyzeNode(node, context)

            if self.WaitCall or context.stop:
                continue

            if node.type == NodeType.IF or node.type == NodeType.IFLOOP:
                self.process_if_node(context, node, current_work_list)
            elif node.type == NodeType.PLACEHOLDER:
                current_work_list.clear()
            else:
                self.process_general_node(context, node, current_work_list)

        return
    
            
    def process_if_node(self, context:FFuncContext, node:Node, work_list):
        if node.type == NodeType.IF:
            true_son, false_son = node.son_true, node.son_false
            true_context, false_context = context.copy(), context.copy()

            true_context.node_path.append(true_son)
            true_context.push_cond(context.cond_expr_if, True)
            if self.Check_constraint(simplify(And(true_context.globalFuncConstraint, true_context.branch_cond))):
                work_list.append((true_context, true_son))

            false_context.node_path.append(false_son)
            false_context.push_cond(context.cond_expr_if, False)
            if self.Check_constraint(simplify(And(false_context.globalFuncConstraint, false_context.branch_cond))):
                work_list.append((false_context, false_son))
        elif node.type == NodeType.IFLOOP:
            # enter loop body
            true_son, false_son = node.son_true, node.son_false
            true_context, false_context = context.copy(), context.copy()

            true_context.node_path.append(true_son)
            false_context.node_path.append(false_son)
            # true_context.push_cond(context.cond_expr_if, True)
            if context.loop_count[node] > config.max_iter:
                work_list.append((false_context, false_son))
                # should warning users here
                logger.warning(f"Loop Node {node.node_id} has exceeded the maximum iteration limit ({config.max_iter}), skipping the rest of the analysis.")
            else:
                if self.Check_constraint(simplify(And(true_context.globalFuncConstraint, context.cond_expr_if))):
                    work_list.append((true_context, true_son))
                else:
                    
                    work_list.append((false_context, false_son))


    def process_general_node(self, context, node, work_list):
        if len(node.sons) == 0 and node.type in [NodeType.ENDIF, NodeType.ENDLOOP]:
            context.pop_cond()
            return
        for son in node.sons:
            new_context = context.copy()
            new_context.node_path.append(son)
            if node.type == NodeType.ENDIF:
                new_context.pop_cond()
            work_list.append((new_context, son))