from typing import List, Dict, Any
from collections import defaultdict
from slither.core.declarations import (
    Function, 
    Contract, 
) 
from slither.core.cfg.node import NodeType, Node
from slither.core.variables import (
    Variable,
)
from slither.slithir.variables import (
    TemporaryVariable,
)
from slither.slithir.operations import(
    Operation,
    BinaryType,
)
from z3 import *
from FFormula import FFormula, ExpressionWithConstraint, Implied_exp


# To maintain the context of the function (call context, constraints, etc.)
class FFuncContext:
    def __init__(self, func:Function, parent_contract:Contract, parent_func:Function=None, caller_node:Node=None, mergeFormulas:Dict[Variable, FFormula]=None, retVarMap: Dict[str, FFormula]=None):
        self.currentFormulaMap: Dict[Variable, FFormula] = {}
        self.globalFuncConstraint = BoolVal(True)
        self.refMap: Dict[Variable, Variable] = {}

        self.caller_node = caller_node
        # means the rest of irs are tackling with return info, and we should delay to analyze them.
        self.callflag = False

        self.returnIRs: List[Operation] = []
        self.callerRetVar: Variable = None
        # name: ret_0, ret_1, ...,  ret_i (especially for TupleVariable)
        self.retVarMap: Dict[str, FFormula] = retVarMap if retVarMap is not None else {}

        self.func = func
        self.parent_contract = parent_contract
        self.parent_func = parent_func
        # for Map and Array, ...
        self.mapVar2Exp: Dict[Variable, ExprRef] = {}
        # map the params to the original args
        # e.g., from1 -> from -> account
        self.mapIndex2Var: Dict[Variable, Variable] = {}
        # merge formulas and only single instance with no copy
        self.mergeFormulas: Dict[Variable, FFormula] = mergeFormulas if mergeFormulas is not None else {}
        # node path
        self.node_path = []
        # conditional jump
        # tracing nested if-else
        self.condition_stack = []
        self.branch_cond = BoolVal(True)
        self.cond_expr_if = BoolVal(True)
        #  stop and give up the current path
        self.stop = False
        # loop count: Node -> int
        self.loop_count = defaultdict(int) 
        # potential callee contract address
        self.temp2addrs: Dict[Variable, Variable] = {}
        # low-level call
        self.low_level_args: Dict[Variable, List[Variable]]= defaultdict(list)

    
    def push_cond(self, conditon:ExprRef, true_or_false:bool):
        actual_cond = conditon if true_or_false else Not(conditon)
        self.condition_stack.append(actual_cond)
        self.update_branch_cond()


    def pop_cond(self):
        if self.condition_stack:
            self.condition_stack.pop()
            self.update_branch_cond()

    
    def update_branch_cond(self):
        if not self.condition_stack:
            self.branch_cond = BoolVal(True)
        else:
            self.branch_cond = simplify(And(*self.condition_stack))

      
    def updateContext(self, var:Variable, fformula:FFormula):
        # need to polish
        self.currentFormulaMap[var] = fformula
        self.currentFormulaMap[var].expressions_with_constraints = list(set(self.currentFormulaMap[var].expressions_with_constraints))


    def deleteContext(self, var:Variable):
        if var in self.currentFormulaMap:
            del self.currentFormulaMap[var]

    
    def mergeFormula(self, var:Variable, fformula:FFormula):
        if var in self.mergeFormulas:
            for exp, cons in fformula.expressions_with_constraints:
                self.mergeFormulas[var].expressions_with_constraints.append(ExpressionWithConstraint(exp, simplify(Implied_exp(self.globalFuncConstraint, cons))))
            # delete redundant expressions
            self.mergeFormulas[var].expressions_with_constraints = list(set(self.mergeFormulas[var].expressions_with_constraints))
        else:
            self.mergeFormulas[var] = FFormula(fformula.stateVar, fformula.parent_contract, fformula.parent_function)
            for exp, cons in fformula.expressions_with_constraints:
                self.mergeFormulas[var].expressions_with_constraints.append(ExpressionWithConstraint(exp, simplify(Implied_exp(self.globalFuncConstraint, cons))))
            # delete redundant expressions
            self.mergeFormulas[var].expressions_with_constraints = list(set(self.mergeFormulas[var].expressions_with_constraints)) # type: ignore


    def clearTempVariableCache(self):
        self.returnIRs = []
        self.callerRetVar = None
        variables_to_delete = []
        for var in self.currentFormulaMap.keys():
            if isinstance(var, TemporaryVariable): # type: ignore
                variables_to_delete.append(var)
        for var in variables_to_delete:
            self.deleteContext(var)
        self.clearRefMap()
        self.temp2addrs.clear()


    def clearRefMap(self):
        self.refMap.clear()


    def copy(self):
        new_context = FFuncContext(self.func, self.parent_contract, self.parent_func, self.caller_node, self.mergeFormulas, self.retVarMap)
        new_context.currentFormulaMap = {var: fformula.copy() for var, fformula in self.currentFormulaMap.items()}
        new_context.returnIRs = self.returnIRs
        new_context.callerRetVar = self.callerRetVar
        new_context.globalFuncConstraint = self.globalFuncConstraint
        new_context.refMap = {var: ref for var, ref in self.refMap.items()}
        new_context.mapVar2Exp = {var: exp for var, exp in self.mapVar2Exp.items()}
        new_context.mapIndex2Var = {var: index_var for var, index_var in self.mapIndex2Var.items()}
        new_context.node_path = self.node_path.copy()
        new_context.condition_stack = self.condition_stack.copy()
        new_context.branch_cond = self.branch_cond
        new_context.cond_expr_if = self.cond_expr_if
        new_context.loop_count = self.loop_count.copy()
        new_context.temp2addrs = {var: addr for var, addr in self.temp2addrs.items()}
        return new_context
    
