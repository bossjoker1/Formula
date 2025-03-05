from z3 import ExprRef, Solver
from typing import NamedTuple, List, Any, Union
from slither.core.variables import StateVariable, Variable
from slither.slithir.operations import HighLevelCall


class ExpressionWithConstraint(NamedTuple):
    expression: ExprRef
    constraint: ExprRef


class FStateVar(NamedTuple):
    contract: Any
    stateVar: Variable

# uncompleted
class FHighLevelCall:
    def __init__(self, contract, func, call:HighLevelCall):
        self.highlevelCall = call
        self.parent_contract = contract
        self.parent_function = func


Fkey = Union[FStateVar, FHighLevelCall]


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
        result = ""
        for expr_with_constraint in list(set(self.expressions_with_constraints)):
            result += f"Expression: {expr_with_constraint.expression}, Constraint: {expr_with_constraint.constraint}"
        return result
    

    def setFormula(self):
        return list(set(self.expressions_with_constraints))
    


# for Map/Member/Array
class FMap(Variable):
    def __init__(self, map:Variable, index:Variable, ttype):
        super().__init__()
        self._map = map
        self._index = index
        self._name = f"{map.name}[{index.name}]"
        self._type = ttype


    def __str__(self):
        return f"{self.map.name}[{self.index.name}]"
    
    
    @property
    def map(self):
        return self._map
    
    
    @property
    def index(self):
        return self._index
    

    def __eq__(self, other):
        if isinstance(other, FMap):
            return (self.map == other.map and
                    self.index == other.index and
                    self.type == other.type)
        return False
    

    def __hash__(self):
        return hash((self.map, self.index, self.type))



# for tuple unpacking
class FTuple(Variable):
    def __init__(self, tuple:Variable, index:int, ttype=None):
        super().__init__()
        self._tuple = tuple
        self._index = index
        self._name = f"{tuple.name}.({index})"
        self._type = ttype


    def __str__(self):
        return f"{self.tuple.name}[{self.index}]"
    
    
    @property
    def tuple(self):
        return self._tuple
    
    
    @property
    def index(self):
        return self._index
    
    
    def __eq__(self, other):
        if isinstance(other, FTuple):
            return (self.tuple == other.tuple and
                    self.index == other.index and
                    self.type == other.type)
        return False
    

    def __hash__(self):
        return hash((self.tuple, self.index, self.type))