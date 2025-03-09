from z3 import *
from typing import NamedTuple, List, Any, Union, Optional
from slither.core.variables import StateVariable, Variable
from slither.slithir.operations import HighLevelCall


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
    

