from typing import List, Dict, Any
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
from FFormula import FFormula


# To maintain the context of the function (call context, constraints, etc.)
class FFuncContext:
    def __init__(self, func:Function, parent_contract:Contract, parent_func:Function=None, caller_node:Node=None):
        self.currentFormulaMap: Dict[Variable, FFormula] = {}
        self.globalFuncConstraint = True
        self.refMap: Dict[Variable, Variable] = {}

        self.caller_node = caller_node
        # means the rest of irs are tackling with return info, and we should delay to analyze them.
        self.callflag = False

        self.returnIRs: List[Operation] = []
        self.callerRetVar: Variable = None
        # name: ret_0, ret_1, ...,  ret_i (especially for TupleVariable)
        self.retVarMap: Dict[str, FFormula] = {}

        self.func = func
        self.parent_contract = parent_contract
        self.parent_func = parent_func
        # for Map and Array, ...
        self.mapVar2Exp: Dict[Variable, ExprRef] = {}
        # map the params to the original args
        # e.g., from1 -> from -> account
        self.mapIndex2Var: Dict[Variable, Variable] = {}
        # node path
        self.node_path = []
        # conditional jump
        # tracing nested if-else
        self.condition_stack = []
        self.branch_cond = BoolVal(True)
        self.cond_expr_if = BoolVal(True)

    
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


    def deleteContext(self, var:Variable):
        if var in self.currentFormulaMap:
            del self.currentFormulaMap[var]


    def clearTempVariableCache(self):
        self.returnIRs = []
        self.callerRetVar = None
        variables_to_delete = []
        for var in self.currentFormulaMap.keys():
            if isinstance(var, TemporaryVariable):
                variables_to_delete.append(var)
        for var in variables_to_delete:
            self.deleteContext(var)
        self.clearRefMap()


    def clearRefMap(self):
        self.refMap.clear()


    def check_constraint(self, cons) -> bool:
        solver = Solver()
        solver.add(cons)
        res = solver.check()
        return res == sat


    def copy(self):
        new_context = FFuncContext(self.func, self.parent_contract, self.parent_func, self.caller_node)
        new_context.currentFormulaMap = {var: fformula.copy() for var, fformula in self.currentFormulaMap.items()}
        new_context.retVarMap = {var: fformula.copy() for var, fformula in self.retVarMap.items()}
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
        return new_context
    
