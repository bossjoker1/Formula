import hashlib
from loguru import logger
from slither.slither import Slither
from slither.core.declarations.contract import Contract
from typing import List
from z3 import BitVecVal
from Function import FFunction

class FContract:
    def __init__(self, sli_contract:Contract, path:str, name:str, slith_all=None, refined=False):
        self.sli_contract = sli_contract
        self.solpath = path
        self.main_name = name
        self._address_this = self.fakeThisAddress()
        self.slither_all = slith_all
        self.refined_formula = refined


    # generate a fake address for this contract based on self.parent_contract.main_name&solpath
    def fakeThisAddress(self):
        unique_string = self.main_name + self.solpath
        # Generate a SHA-256 hash of the unique string
        hash_object = hashlib.sha256(unique_string.encode())
        # Get the first 20 bytes (160 bits) of the hash
        hash_bytes = hash_object.digest()[:20]
        # Convert the bytes to an integer
        hash_int = int.from_bytes(hash_bytes, byteorder='big')
        # Create a BitVecVal with the integer value
        fake_address = BitVecVal(hash_int, 160)
        return fake_address
    
    
    @property
    def address_this(self):
        return self._address_this


    def __str__(self):
        return f"Contract: [{self.main_name}] at {self.solpath}"



# ================================================================

def BuildFormula(contract_pairs, refined):
    for path, main_name in contract_pairs:
        logger.debug(f"Building formula for contract {main_name} at path {path}")
        slither = Slither(path)
        sli_contract = slither.get_contract_from_name(main_name)[0]
        fcontract = FContract(sli_contract, path, main_name, slither, refined=refined)
        for func in fcontract.sli_contract.functions:
            # only care about public/external functions
            ffunc = FFunction(func, fcontract)
            # logger.debug(f"[F] function name:  {ffunc.func.canonical_name}")
            # IF branch test: AEST._transfer(address,address,uint256)
            # ERC20._transfer(address,address,uint256)
            # AEST.conTest()
            if ffunc.func.canonical_name == "AEST._transfer(address,address,uint256)":
                print(ffunc)
                ffunc.buildCFG()
                ffunc.printFFormulaMap()