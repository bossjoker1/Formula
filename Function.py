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
    LowLevelCall,
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
    Length,
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
        self.highlevelCalls = self.func.all_high_level_calls()
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


    def printFFormulaMap(self, context:FFuncContext):
        print(f"Contract: [{self.parent_contract.main_name}], Function: <{self.func.canonical_name}>")

        formula_set = set()

        for stateVar, fformula in self.FormulaMap.items():
            
            if len(fformula.expressions_with_constraints) == 0:
                continue

            if stateVar in formula_set:
                continue
            formula_set.add(stateVar)
                
            var = stateVar.stateVar
            if not isinstance(var, FMap):
                self._log_state_var(var.name, fformula)
                continue
            
                
            if var.index not in context.currentFormulaMap.keys():
                self._log_state_var(var.name, fformula)
                continue
                
            exps = context.currentFormulaMap[var.index].expressions_with_constraints
            if not exps:
                self._log_state_var(var.name, fformula)
                continue
                
            for exp, _ in exps:
                if isinstance(var.map, FMap):
                    if var.map.index in context.currentFormulaMap.keys():
                        inner_exps = context.currentFormulaMap[var.map.index].expressions_with_constraints
                        if inner_exps:
                            for iexp, _ in inner_exps:
                                self._log_state_var(f"{var.map.map_name}[{iexp}][{exp}]", fformula)
                        else:
                            self._log_state_var(f"{var.map.map_name}[{var.map.index.name}][{exp}]", fformula)
                    else:
                        self._log_state_var(f"{var.map.map_name}[{var.map.index.name}][{exp}]", fformula)
                else:
                    self._log_state_var(f"{var.map_name}[{exp}]", fformula)


    def _log_state_var(self, var_name: str, fformula: FFormula):
        print(f"StateVar: {var_name}, formula: {fformula}")


    def __str__(self):
        return f"Function: [{self.func.name}] in contract [{self.parent_contract.main_name}]"


    def analyzeNode(self, node: Node, context:FFuncContext):
        # del formula map of temp variable
        # context.clearTempVariableCache()
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
                    if isinstance(var, StateVariable) or (isinstance(var, FMap) and (isinstance(var.map, StateVariable) or isinstance(var.map, FMap))):
                        self.addFFormula(FStateVar(self.parent_contract, var), formula, context, repeat=True)

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
        from slither.slithir.operations import Length
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

        
        elif isinstance(ir, Length):
            self.handleLengthIR(ir, context)


    def handleLengthIR(self, ir:Length, context:FFuncContext):
        var = self.getRefPointsTo(ir.value, context)
        var_exp = Int(var.name + ".length")
        # special case
        context.refMap[ir.lvalue] = ir.lvalue
        fformula = FFormula(FStateVar(self.parent_contract, ir.lvalue), self.parent_contract, self)
        fformula.expressions_with_constraints = [ExpressionWithConstraint(var_exp, True)]
        context.updateContext(ir.lvalue, fformula)
        return


    def handleConditionIR(self, ir:Condition, context:FFuncContext):
        cond = self.getRefPointsTo(ir.value, context)
        cond_expr = self.handleVariableExpr(cond, context)
        cond_expr_if = Reconstruct_If(cond_expr)
        context.cond_expr_if = simplify(cond_expr_if)
        

    def handleUnpackIR(self, ir:Unpack, context:FFuncContext):
        lvalue = self.getRefPointsTo(ir.lvalue, context)
        tuple_var = FTuple(ir.tuple, ir.index, ir.tuple.type[ir.index])
        rexp = self.handleVariableExpr(tuple_var, context)
        if lvalue not in context.currentFormulaMap:
            fformula = FFormula(FStateVar(self.parent_contract, lvalue), self.parent_contract, self)
            fformula.expressions_with_constraints = rexp
            context.updateContext(lvalue, fformula)
        else:
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
        if isinstance(ir, SolidityCall) and (ir.function in [
            SolidityFunction("require(bool,string)"), 
            SolidityFunction("require(bool)"),
            SolidityFunction("require(bool,error)"),
            SolidityFunction("assert(bool)"),
            SolidityFunction("revert()"),
            SolidityFunction("revert(string)"),
        ] or ir.function.full_name in [
            "abi.encodeWithSelector()"
        ]): 
            
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
            
            elif ir.function.full_name in [
                "abi.encodeWithSelector()"
            ]:
                # record selector and arguments
                lvalue, args = ir.lvalue, ir.arguments
                context.low_level_args[lvalue] = args
                return
       
        elif isinstance(ir, InternalCall) or isinstance(ir, HighLevelCall) or isinstance(ir, LowLevelCall):
            # if ir.is_modifier_call:
            #     continue
            # highlevel call requires more processing     
            callee_func, callee_context = None, None
            if (isinstance(ir, HighLevelCall) and not isinstance(ir, LibraryCall)) or isinstance(ir, LowLevelCall):
                # ignore set
                # return
                if not isinstance(ir, LowLevelCall):
                    callee_func = ir.function
                # get callee contract variable
                dest = context.temp2addrs[ir.destination] if ir.destination in context.temp2addrs.keys() else ir.destination
                # try to get callee contract address
                callee_addr = self.parent_contract.online_helper.get_contract_address(dest, context, context.parent_contract.address)
                if callee_addr:
                    from Contract import FContract
                    if callee_addr in self.parent_contract.online_helper.cached_contracts.keys():
                        logger.debug(f"hit the cached contract: {callee_addr}")
                        callee_contract = self.parent_contract.online_helper.cached_contracts[callee_addr]
                        sli_contract = callee_contract.sli_contract
                    else:
                        callee_info = self.parent_contract.online_helper.get_contract_sourcecode(callee_addr)
                        sli_contract = self.parent_contract.online_helper.get_slither_contract(callee_info)
                        callee_contract = FContract(sli_contract=sli_contract, path=callee_info["contract_file"], name=callee_info["contract_name"], online_helper=self.parent_contract.online_helper, address=callee_addr)
                        self.parent_contract.online_helper.cached_contracts[callee_addr] = callee_contract
                    if isinstance(ir, LowLevelCall):
                        try:
                            selector = self.parent_contract.online_helper.get4bytesinfo(hex(context.low_level_args[ir.arguments[0]][0].value))
                            func = sli_contract.get_function_from_signature(selector)
                        except Exception as e:
                            logger.warning(f"Error in getting function from selector: {e}")
                            func = None
                            return
                        finally:
                            if not func:
                                return
                    else:
                        func = sli_contract.get_function_from_full_name(ir.function.full_name)
                    callee_func = func
                    callee_context = FFuncContext(func=func, parent_contract=callee_contract, parent_func=context.func, caller_node=ir.node)
            else:
                if ir.function.canonical_name == "Math.sqrt(uint256)":
                    sqrt = Function('sqrt', IntSort(), IntSort())
                    temp_var = ir.lvalue
                    formula = FFormula(FStateVar(self.parent_contract, temp_var), self.parent_contract, self)
                    context.updateContext(temp_var, formula)
                    var = self.getRefPointsTo(ir.arguments[0], context)
                    # apply sqrt
                    for exp, cons in self.handleVariableExpr(var, context):
                        sqrt_exp = sqrt(exp)
                        context.currentFormulaMap[temp_var].expressions_with_constraints.append(ExpressionWithConstraint(sqrt_exp, cons))
                    return
                callee_context = FFuncContext(func=ir.function, parent_contract=context.parent_contract, parent_func=context.func, caller_node=ir.node)
                callee_func = ir.function
            if not callee_context:
                logger.warning(f"something wrong with callee context: {ir}")
                return
                # callee_context = FFuncContext(func=ir.function, parent_contract=context.parent_contract, parent_func=context.func, caller_node=ir.node)
            # shoud AND if_cond when calling 
            callee_context.globalFuncConstraint = simplify(self.Implied_exp(context.globalFuncConstraint, context.branch_cond))
            if not self.Check_constraint(callee_context.globalFuncConstraint):
                context.stop = True
                return
            # add state variable context
            temp_context = context.copy()
            temp_context.clearRefMap()
            # temp_context.clearTempVariableCache()
            callee_context.currentFormulaMap = temp_context.currentFormulaMap
            # map args to params
            self.mapArgsToParams(ir, callee_func, context, callee_context)
            self.pushCallStack(ir, callee_func, context, callee_context)
            self.WaitCall = True
            context.callflag = True
            if ir.lvalue:
                context.callerRetVar = self.getRefPointsTo(ir.lvalue, context)


    def pushCallStack(self, ir:Call, func:Function, context:FFuncContext, callee_context:FFuncContext):
        self.call_stack.append((context, [(callee_context, func.entry_point)]))


    # TODO: not good enough
    def mapArgsToParams(self, ir:Call, func:Function, context:FFuncContext, callee_context:FFuncContext):
        for arg, param in zip(ir.arguments, func.parameters):
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
        converted_exps = []
        for exp, cons in rexp:
            if is_int(exp) and (ir.type == ElementaryType("address") or ir.type.storage_size[0] == 20):
                converted_exp = Int2BV(exp, 160)
            else:
                if is_int_value(exp) and exp == IntVal(-1):
                    converted_exp = IntVal(2**112 - 1)
                else:
                    converted_exp = exp
            converted_exps.append(ExpressionWithConstraint(converted_exp, cons))
        fformula = FFormula(FStateVar(self.parent_contract, ir.lvalue), self.parent_contract, self)
        fformula.expressions_with_constraints = converted_exps
        context.updateContext(ir.lvalue, fformula)
        
        # storage potential callee contract address
        if not (rvalue.type == ElementaryType("address") or rvalue.type.storage_size[0] == 20):
            return

        context.temp2addrs[ir.lvalue] = rvalue
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
        var, idx = self.getRefPointsTo(ir.variable_left, context), self.getRefPointsTo(ir.variable_right, context)
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
        var, idx = self.getRefPointsTo(ir.variable_left, context), self.getRefPointsTo(ir.variable_right, context)
        ref = ir.lvalue
        if isinstance(var.type, MappingType):
            type_from, type_to = var.type.type_from, var.type.type_to
            type2type = {
                ElementaryType("uint256"): IntSort(),
                ElementaryType("bool"): BoolSort(),
                ElementaryType("string"): StringSort(),
                ElementaryType("address"): BitVecSort(160),
            }
            
            map_from = type2type.get(type_from, IntSort())
            
            if isinstance(type_to, MappingType):
                inner_type_from, inner_type_to = type_to.type_from, type_to.type_to
                if isinstance(inner_type_from, MappingType):
                    logger.warning(f"There is a more than 2-level mapping in the map type: {var.name}")
                inner_map_from = type2type.get(inner_type_from, IntSort())
                inner_map_to = type2type.get(inner_type_to, IntSort())
                
                if idx in context.mapIndex2Var.keys():
                    first_map_var = FMap(var, context.mapIndex2Var[idx], type_to)
                else:
                    first_map_var = FMap(var, idx, type_to)
                context.refMap[ref] = first_map_var
                
                if first_map_var not in context.currentFormulaMap:
                    fformula = FFormula(FStateVar(self.parent_contract, first_map_var), self.parent_contract, self)
                    idx_exprs = self.handleVariableExpr(idx, context)
                    if idx_exprs:
                        new_exprs = []
                        for idx_exp, idx_cons in idx_exprs:
                            select_exp = Select(Array(f"{var.name}", map_from, ArraySort(inner_map_from, inner_map_to)), idx_exp)
                            if not self.Check_constraint(self.Implied_exp(context.branch_cond, self.Implied_exp(idx_cons, context.globalFuncConstraint))):
                                continue
                            new_exprs.append(ExpressionWithConstraint(select_exp, idx_cons))
                        fformula.expressions_with_constraints = new_exprs
                    context.updateContext(first_map_var, fformula)
            else:
                map_to = type2type.get(type_to, IntSort())
                if idx in context.mapIndex2Var.keys():
                    map_var = FMap(var, context.mapIndex2Var[idx], ref.type)
                else:
                    map_var = FMap(var, idx, ref.type)
                    
                if isinstance(ref, ReferenceVariable):
                    context.refMap[ref] = map_var
                    if map_var not in context.currentFormulaMap:
                        fformula = FFormula(FStateVar(self.parent_contract, map_var), self.parent_contract, self)
                        idx_exprs = self.handleVariableExpr(idx, context)
                        if idx_exprs:
                            new_exprs = []
                            if isinstance(var, FMap):
                                if var in context.currentFormulaMap:
                                    for var_exp, var_cons in context.currentFormulaMap[var].expressions_with_constraints:
                                        for idx_exp, idx_cons in idx_exprs:
                                            combined_cons = self.Implied_exp(context.branch_cond, self.Implied_exp(self.Implied_exp(var_cons, idx_cons), context.globalFuncConstraint))
                                            if not self.Check_constraint(combined_cons):
                                                continue
                                            select_exp = Select(var_exp, idx_exp)
                                            new_exprs.append(ExpressionWithConstraint(select_exp, combined_cons))
                                else:
                                    for idx_exp, idx_cons in idx_exprs:
                                        select_exp = Select(Array(f"{var.name}", map_from, map_to), idx_exp)
                                        new_exprs.append(ExpressionWithConstraint(select_exp, idx_cons))
                            else:
                                logger.debug(f"map_from: {map_from}, map_to: {map_to}")
                                for idx_exp, idx_cons in idx_exprs:
                                    if is_int(idx_exp) and is_bv_sort(map_from):
                                        logger.debug(f"idx_exp: {idx_exp}, type: {type(idx_exp)}")
                                        # idx_exp = 
                                    select_exp = Select(Array(f"{var.name}", map_from, map_to), idx_exp)
                                    new_exprs.append(ExpressionWithConstraint(select_exp, idx_cons))
                            fformula.expressions_with_constraints = new_exprs
                        context.updateContext(map_var, fformula)
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
            l_expr, r_expr = litem.expression, ritem.expression
            if op.__name__ == '<lambda>' and op.__code__.co_code == (lambda x, y: x % y).__code__.co_code:
                if isinstance(l_expr, RatNumRef):
                    l_expr = ToInt(l_expr)
                if isinstance(r_expr, RatNumRef):
                    r_expr = ToInt(r_expr)
            combined_expr = simplify(op(l_expr, r_expr))
            if combined_expr == None:
                logger.error(f"Error in merging expressions: {l_expr} and {r_expr}")
            combined_constraint = simplify(self.Implied_exp(litem.constraint, ritem.constraint))
            if not self.Check_constraint(combined_constraint):
                continue
            res.append(ExpressionWithConstraint(combined_expr, combined_constraint))
        # constaints are not satisfied, discard this branch
        if len(res) == 0:
            context.stop = True
        return res
    

    def assignSymbolicVal(self, var:Variable):
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
        elif var.type.storage_size[0] == 20:
            formula = BitVec(var.name, 160)
        else:
            formula = Int(var.name)

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
                for exp, cons in context.currentFormulaMap[var].expressions_with_constraints:
                    if exp == None:
                        continue
                    expressions_with_constraints.append(ExpressionWithConstraint(exp, cons))
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
            if 'ret_0' in callee_context.retVarMap:
                fformula.expressions_with_constraints = callee_context.retVarMap['ret_0'].expressions_with_constraints.copy()
            else:
                fformula.expressions_with_constraints = self.handleVariableExpr(callerRetVar, caller_context)
            caller_context.updateContext(callerRetVar, fformula)
        elif isinstance(callerRetVar, TupleVariable):
            # assert len(callee_context.retVarMap.keys()) > 0
            for idx in range(len(callee_context.retVarMap.keys())):
                ret_idx = f"ret_{idx}"
                tuple_var = FTuple(callerRetVar, idx, callerRetVar.type[idx])
                fformula = FFormula(FStateVar(self.parent_contract, tuple_var), self.parent_contract, self)
                if ret_idx in callee_context.retVarMap:
                    fformula.expressions_with_constraints = callee_context.retVarMap[ret_idx].expressions_with_constraints.copy()
                else:
                    fformula.expressions_with_constraints = self.handleVariableExpr(tuple_var, caller_context)
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
            if isinstance(var, StateVariable) or (isinstance(var, FMap) and (isinstance(var.map, StateVariable) or isinstance(var.map, FMap))):
                if isinstance(var, FMap) and var.index in callee_context.mapIndex2Var:
                    var = FMap(var.map, callee_context.mapIndex2Var[var.index], var.type)
                caller_context.currentFormulaMap[var] = formula
                if isinstance(var, FMap):
                    # should update here
                    if var.index in callee_context.mergeFormulas:
                        caller_context.currentFormulaMap[var.index] = callee_context.mergeFormulas[var.index]
                        if isinstance(var.map, FMap):
                            if var.map.index in callee_context.mergeFormulas:
                                caller_context.currentFormulaMap[var.map.index] = callee_context.mergeFormulas[var.map.index]


        if self.is_terminal_node(callee_context.caller_node):
            for var, formula in caller_context.currentFormulaMap.items():
                if len(formula.expressions_with_constraints) == 0:
                    continue
                if isinstance(var, StateVariable) or (isinstance(var, FMap) and (isinstance(var.map, StateVariable) or isinstance(var.map, FMap))):
                    if isinstance(var, FMap) and var.index in callee_context.mapIndex2Var:
                        var = FMap(var.map, caller_context.mapIndex2Var[var.index], var.type)
                    self.addFFormula(FStateVar(self.parent_contract, var), formula)

        return False
    

    def printNodeInfo(self, context:FFuncContext, node:Node):
        if not node:
            return
        logger.debug(f"[N] Parent Function: {context.parent_func.canonical_name if context.parent_func else 'None'} \n [N] Current Function <{context.func.canonical_name}> Processing node {node} {node.node_id}")
        for ir in node.irs:
            logger.debug(f"----- ir[{type(ir)}] : {ir}")


    def printHighlevelCalls(self):
        print("Highlevel_calls: ")
        for contract, call in self.highlevelCalls:
            # print call
            print(call.function.canonical_name)

                          
    # reorder basic blocks(nodes) of function (especially for those have modifiers)
    # pass Context to the son nodes
    def buildCFG(self):
        context = FFuncContext(func=self.func, parent_contract=self.parent_contract)
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
            if not node:
                continue
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

        self.printFFormulaMap(context)

        self.printHighlevelCalls()

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
                logger.warning(f"Loop Node {node} has exceeded the maximum iteration limit ({config.max_iter}), skipping the rest of the analysis.")
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

            