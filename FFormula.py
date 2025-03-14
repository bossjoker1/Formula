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

def Check_constraint(cons) -> bool:
    solver = Solver()
    solver.add(cons)
    res = solver.check()
    return res == sat


def Implied_exp(expr1, expr2, refined=False):
    if refined:
        solver = Solver()
        solver.add(And(expr1, Not(expr2)))
        res_1 = solver.check() == unsat
        solver.reset()
        solver.add(And(expr2, Not(expr1)))
        res_2 = solver.check() == unsat
        if res_1:
            return expr1
        elif res_2:
            return expr2
        else:
            return And(expr1, expr2)
    else:
        return And(expr1, expr2)

def Reconstruct_If(exprs_with_constraints: List[ExpressionWithConstraint]) -> Optional[ExprRef]:
        if not exprs_with_constraints:
            return None
        head = None
        for expr, cond in reversed(exprs_with_constraints):
            if head is None:
                head = If(cond, expr, BoolVal(False))
            else:
                head = If(cond, expr, head)
        if is_false(simplify(head)):
            return Not(cond)
        elif is_true(simplify(head)):
            return cond
        else:
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
    
