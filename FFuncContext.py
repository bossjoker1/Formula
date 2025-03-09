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


binary_op = {
            BinaryType.ADDITION: lambda x, y: x + y,
            BinaryType.SUBTRACTION: lambda x, y: x - y,
            BinaryType.MULTIPLICATION: lambda x, y: x * y,
            BinaryType.DIVISION: lambda x, y: x / y,
            BinaryType.MODULO: lambda x, y: x % y,
            BinaryType.EQUAL: lambda x, y: x == y,
            BinaryType.NOT_EQUAL: lambda x, y: x != y,
            BinaryType.LESS: lambda x, y: x < y,
            BinaryType.LESS_EQUAL: lambda x, y: x <= y,
            BinaryType.GREATER: lambda x, y: x > y,
            BinaryType.GREATER_EQUAL: lambda x, y: x >= y,
            BinaryType.ANDAND: lambda x, y: And(x, y),
            BinaryType.OROR: lambda x, y: Or(x, y),
            BinaryType.AND: lambda x, y: x & y,
            BinaryType.OR: lambda x, y: x | y,
            BinaryType.CARET: lambda x, y: x ^ y,
            BinaryType.LEFT_SHIFT: lambda x, y: x << y,
            BinaryType.RIGHT_SHIFT: lambda x, y: LShR(x, y),
            BinaryType.POWER: lambda x, y: x ** y
        }


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
        return new_context
    
