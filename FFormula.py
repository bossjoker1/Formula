from loguru import logger
from z3 import *
from typing import NamedTuple, List, Any, Union, Optional
from slither.core.variables import StateVariable, Variable
from slither.slithir.operations import BinaryType
from slither.core.solidity_types import (
    ElementaryType,
    MappingType,
)


class ExpressionWithConstraint(NamedTuple):
    expression: ExprRef
    constraint: ExprRef


class FStateVar(NamedTuple):
    contract: Any
    stateVar: Variable


class FFormula:
    def __init__(self, stateVar:FStateVar, contract=None, func=None):
        self.stateVar = stateVar
        self.parent_contract = contract
        self.parent_function = func
        self.expressions_with_constraints : List[ExpressionWithConstraint] = []


    def add_expression_with_constraint(self, expression: ExprRef, constraint: ExprRef):
        self.expressions_with_constraints.append(ExpressionWithConstraint(expression, constraint))
        

    def copy(self):
        new_formula = FFormula(self.stateVar, self.parent_contract, self.parent_function)
        new_formula.expressions_with_constraints = [ExpressionWithConstraint(expr.expression, expr.constraint) for expr in self.expressions_with_constraints]
        return new_formula
    

    def __str__(self):
        result = "\n"
        for idx, expr_with_constraint in enumerate(list(set(self.expressions_with_constraints))):
            result += f"Expression [{idx}]: {expr_with_constraint.expression}, \nConstraint [{idx}]: {expr_with_constraint.constraint}\n"
        return result
    

    def setFormula(self):
        return list(set(self.expressions_with_constraints))
    

# ==============================================================================================================
# export functions:
def Reconstruct_If(exprs_with_constraints: List[ExpressionWithConstraint]) -> Optional[ExprRef]:
        if not exprs_with_constraints:
            return None
        head = None
        for expr, cond in reversed(exprs_with_constraints):
            if head is None:
                head = If(cond, expr, BoolVal(False))
            else:
                head = If(cond, expr, head)
        return head


def Expand_If(expr: ExprRef, cond: ExprRef) -> List[ExpressionWithConstraint]:
    expressions = []
    stack = [expr]
    while stack:
        current_expr = stack.pop()
        if is_app_of(current_expr, Z3_OP_ITE):
            true_expr = ExpressionWithConstraint(expression=current_expr.arg(1), constraint=simplify(And(cond, current_expr.arg(0))))
            expressions.append(true_expr)
            stack.append(current_expr.arg(2))
        else:
            expressions.append(ExpressionWithConstraint(expression=current_expr, constraint=cond))
    return expressions
    

NONE_FORMULA = IntVal(-1*2**256)


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


class Formula:
    def __init__(self, stateVar:FStateVar=None, contract=None, func=None):
        self.stateVar = stateVar
        self.parent_contract = contract
        self.parent_function = func
        self.expressions_with_constraints: Optional[ExprRef] = None


    def init_expr(self):
        self.expressions_with_constraints = self.getSymbolicValue()


    def getSymbolicValue(self):
        formula = None

        if self.stateVar.stateVar.type == ElementaryType("uint256"):
            formula = Int(self.stateVar.stateVar.name)
        elif self.stateVar.stateVar.type == ElementaryType("bool"):
            formula = Bool(self.stateVar.stateVar.name)
        elif self.stateVar.stateVar.type == ElementaryType("string"):
            formula = String(self.stateVar.stateVar.name)
        elif self.stateVar.stateVar.type == ElementaryType("address"):
            formula = BitVec(self.stateVar.stateVar.name, 160)

        if formula == None:
            logger.error(f"Error in getting symbolic value for {self.stateVar.stateVar}")

        return formula


    def set_exprs(self, expr: ExprRef, cond: ExprRef = True) -> Optional[ExprRef]:
        if is_app_of(expr, Z3_OP_ITE):
            self.expressions_with_constraints = self.reconstruct_if(self._expand_if(expr, cond))
        else:
            self.expressions_with_constraints = If(simplify(cond), expr, NONE_FORMULA)


    def _expand_if(self, expr: ExprRef, cond: ExprRef) -> List[ExpressionWithConstraint]:
        expressions = []
        stack = [expr]
        while stack:
            current_expr = stack.pop()
            if is_app_of(current_expr, Z3_OP_ITE):
                true_expr = ExpressionWithConstraint(expression=current_expr.arg(1), constraint=simplify(And(cond, current_expr.arg(0))))
                expressions.append(true_expr)
                stack.append(current_expr.arg(2))
        return expressions
    

    def reconstruct_if(self, exprs_with_constraints: List[ExpressionWithConstraint]) -> Optional[ExprRef]:
        if exprs_with_constraints is None:
            return None
        return self._reconstruct_if(exprs_with_constraints)

    
    def _reconstruct_if(self, exprs_with_constraints: List[ExpressionWithConstraint]) -> Optional[ExprRef]:
        if not exprs_with_constraints:
            raise ValueError("Expression list is empty")
        head = None
        for expr, cond in reversed(exprs_with_constraints):
            if head is None:
                head = If(cond, expr, self.getSymbolicValue())
            else:
                head = If(cond, expr, head)
        return head
    
# ==============================================================================================================   

    

def MergeAndRefineExp(lexp: ExprRef, rexp: ExprRef, op: Any=None, cond: ExprRef=True) -> Optional[ExprRef]:
    lexp_list, rexp_list = Expand_If(lexp, cond), Expand_If(rexp, cond)
    combined_list = []
    if op != None:
        for litem, ritem in zip(lexp_list, rexp_list):
            combined_expr = simplify(op(litem.expression, ritem.expression))
            if combined_expr == None:
                logger.error(f"Error in merging expressions: {litem.expression} and {ritem.expression}")
                return None
            combined_constraint = simplify(And(litem.constraint, ritem.constraint))
            if is_false(combined_constraint):
                continue
            combined_list.append(ExpressionWithConstraint(expression=combined_expr, constraint=combined_constraint))
    else:
        combined_list = lexp_list + rexp_list
        
    return Reconstruct_If(combined_list)


# ==============================================================================================================

def testFormula():
    print("===== testing  Formula and set_exprs =====")
    
    x = Int('x')
    y = Int('y')
    z = Int('z')

    formula = Formula()
    condition_if = If(x > 5, y > 10, z > 15)
    nested_if = If(y > 10, IntVal(300), If(y > 5, IntVal(400), NONE_FORMULA))
    formula.set_exprs(nested_if, condition_if)
    print("[formula 3]:", simplify(formula.expressions_with_constraints))

    formula1 = Formula()
    formula1.set_exprs(IntVal(100), x > 0)
    print("[formula 1]:", formula1.expressions_with_constraints)
    formula2 = Formula()
    formula2.set_exprs(IntVal(400), y < 0)
    merged_expr = MergeAndRefineExp(formula1.expressions_with_constraints, formula2.expressions_with_constraints, lambda x, y: x + y)
    print("[added result]:", simplify(merged_expr))


if __name__ == "__main__":
    testFormula()