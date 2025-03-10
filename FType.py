# for Map/Member/Array
from typing import NamedTuple, List, Any, Union, Optional
from slither.core.variables import StateVariable, Variable
from slither.slithir.operations import(
    Operation,
    BinaryType,
)
from z3 import *


BINARY_OP = {
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
    
    