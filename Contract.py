import hashlib
from loguru import logger
from slither.slither import Slither
from slither.core.declarations.contract import Contract
from typing import List
from z3 import BitVecVal
from Function import FFunction
from Helper import OnlineHelper
from web3 import Web3
import config


class FContract:
    def __init__(self, sli_contract:Contract, path:str="", name:str="", online_helper=None, address:str="0x0"):
        self.sli_contract = sli_contract
        self.solpath = path
        self.main_name = name
        # self.slither_all = slith_all
        if config.mode == "online":
            self.online_helper = online_helper
        else:
            self.online_helper = OnlineHelper("bnb", -1)
        if config.mode == "online":
            self.address = address
            self._address_this = BitVecVal(int(address, 16), 160)
        else:
            self._address_this = self.fakeThisAddress()


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
# online mode
def OnlineBuild(contract_info):
    onlineHelper = OnlineHelper(contract_info["chain"], contract_info["block"])
    w3 = Web3()
    for addr in contract_info["addresses"]:
        addr = w3.to_checksum_address(addr)
        logger.debug(f"Building formula for contract at address {addr}")
        config_info = onlineHelper.get_contract_sourcecode(addr)
        sli_contract = onlineHelper.get_slither_contract(config_info)
        fcontract = FContract(sli_contract=sli_contract, path=config_info["contract_file"], name=config_info["contract_name"], online_helper=onlineHelper, address=addr)
        fcontract.online_helper.cached_contracts[addr] = fcontract
        for func in fcontract.sli_contract.functions:
            ffunc = FFunction(func, fcontract)
            logger.debug(f"[F] function name:  {ffunc.func.canonical_name}")
            # PancakeRouter.addLiquidityETH(address,uint256,uint256,uint256,address,uint256)
            # PancakeRouter.addLiquidity(address,address,uint256,uint256,uint256,uint256,address,uint256)
            # if ffunc.func.canonical_name == "AEST.addInitLiquidity(uint256)":
            #     print(ffunc)
            #     ffunc.buildCFG()
                


# TODO: uncompleted
# offline mode: read from local files
def BuildFormula(contract_pairs):
    for path, main_name in contract_pairs:
        logger.debug(f"Building formula for contract {main_name} at path {path}")
        slither = Slither(path)
        sli_contract = slither.get_contract_from_name(main_name)[0]
        fcontract = FContract(sli_contract, path, main_name)
        for func in fcontract.sli_contract.functions:
            # only care about public/external functions
            ffunc = FFunction(func, fcontract)
            # logger.debug(f"[F] function name:  {ffunc.func.canonical_name}")
            # IF branch test: AEST._transfer(address,address,uint256)
            # ERC20._transfer(address,address,uint256)
            # AEST.conTest()
            # AEST.loopTest()
            # AEST.addInitLiquidity(uint256)
            if ffunc.func.canonical_name == "AEST._transfer(address,address,uint256)":
                print(ffunc)
                ffunc.buildCFG()
                ffunc.printFFormulaMap()