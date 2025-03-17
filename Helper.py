from web3 import Web3
from FFuncContext import FFuncContext
from slither.core.variables import Variable
from slither.core.variables import (
    StateVariable,
)

from z3 import *
from loguru import logger
import requests
import json
import os
import re
import toml

# Load configuration
try:
    with open('config.toml', 'r') as f:
        config = toml.load(f)
    CHAIN_INFO = config['rpc']
    API_KEYS = config['api_keys']
    API_URLS = config['api_urls']
except Exception as e:
    logger.error(f"Failed to load config.toml: {str(e)}")
    raise
# =================================================================


class OnlineHelper:
    def __init__(self, chain: str, block_number: int):
        self.chain = chain
        self.w3 = Web3(Web3.HTTPProvider(CHAIN_INFO[chain]))
        self.block_number = block_number if block_number != -1 else self.get_block_number()


    def get_block_number(self):
        return self.w3.eth.block_number


    def get_contract_address(self, contract_var: Variable, context: FFuncContext, contract_address: str):
        if isinstance(contract_var, StateVariable):
            if not contract_var.visibility != "Public":
                return None
            contract_var_name = contract_var.name
            function_signature = f"{contract_var_name}()"
            function_selector = self.w3.keccak(text=function_signature)[:4].hex()
            try:
                result = self.w3.eth.call({
                    'to': self.w3.to_checksum_address(contract_address),
                    'data': function_selector,
                }, block_identifier=self.block_number)

                address = '0x' + result.hex()[-40:]
                
                if self.w3.is_address(address):
                    return self.w3.to_checksum_address(address)
                else:
                    raise ValueError(f"Invalid address returned for {contract_var_name}")
                    
            except Exception as e:
                logger.warning(f"Failed to get address for {contract_var_name}: {str(e)}")
                return None
            
        else:
            if contract_var in context.currentFormulaMap.keys():
                for exp, cons in context.currentFormulaMap[contract_var].expressions_with_constraints:
                    if not is_const(exp):
                        continue
                    if not (is_bv(exp) or is_int(exp)):
                        continue
                    try:
                        hex_addr = hex(exp.as_long())
                        if self.w3.is_address(hex_addr):
                            return self.w3.to_checksum_address(hex_addr)
                    except Exception as e:
                        logger.warning(f"Failed to convert value to address: {str(e)}")
                        continue
            
        return None
    
    
    def get_contract_sourcecode(self, address: str, save_dir: str = './contracts') -> dict:
        logger.info(f"get contract sourcecode: {address}")
        address = self.w3.to_checksum_address(address)
        
        if not os.path.exists(save_dir):
            os.makedirs(save_dir)
            
        api_url = API_URLS.get(self.chain)
        api_key = API_KEYS.get(self.chain)
        
        if not api_url or not api_key:
            raise ValueError(f"unsupported chain type: {self.chain}")
        
        params = {
            "module": "contract",
            "action": "getsourcecode",
            "address": address,
            "apikey": api_key
        }
        
        try:
            response = requests.get(api_url, params=params)
            data = response.json()
            
            if data["status"] != "1" or not data["result"]:
                logger.error(f"failed to get the contract's source code: {data.get('message', '')}")
                return None
                
            contract_data = data["result"][0]
            
            source_code = contract_data.get("SourceCode", "")
            contract_name = contract_data.get("ContractName", "")
            compiler_version = contract_data.get("CompilerVersion", "").replace("v", "")

            if os.path.exists(os.path.join(save_dir, f"{address[2:8]}_{contract_name}.sol")):
                result = {
                    "address": address,
                    "contract_name": contract_name,
                    "compiler_version": compiler_version,
                    "contract_file": os.path.join(save_dir, f"{address[2:8]}_{contract_name}.sol")
                }        
                return result
            
            # check if it is a standard JSON input or a single file
            if source_code.startswith("{") and source_code.endswith("}"):
                try:
                    if source_code.startswith('{{') and source_code.endswith('}}'):
                        source_code = source_code[1:-1]
                    
                    source_json = json.loads(source_code)
                    
                    if "sources" in source_json:
                        sources = source_json["sources"]
                        contract_dir = os.path.join(save_dir, f"{address[2:8]}")
                        if not os.path.exists(contract_dir):
                            os.makedirs(contract_dir)
                        
                        for file_path, file_info in sources.items():
                            file_content = file_info.get("content", "")
                            
                            clean_path = file_path.replace("/", "_").replace(":", "_")
                            out_path = os.path.join(contract_dir, clean_path)
                            
                            with open(out_path, "w", encoding="utf-8") as f:
                                f.write(file_content)
                            
                            logger.info(f"save the source file: {out_path}")
                            
                        main_file = None
                        for file_path in sources.keys():
                            if contract_name in file_path or re.search(f"[^a-zA-Z0-9]{contract_name}[^a-zA-Z0-9]", file_path):
                                main_file = file_path
                                break
                        
                        result = {
                            "address": address,
                            "contract_name": contract_name,
                            "compiler_version": compiler_version,
                            "contract_dir": contract_dir,
                            "main_file": main_file
                        }
                        
                        return result
                        
                except json.JSONDecodeError:
                    logger.warning("failed to parse the JSON source code, try to handle it as a single file")
            
            
            contract_file = os.path.join(save_dir, f"{address[2:8]}_{contract_name}.sol")
            
            with open(contract_file, "w", encoding="utf-8") as f:
                f.write(source_code)
                
            logger.info(f"save the contract's source code to: {contract_file}")
            
            result = {
                "address": address,
                "contract_name": contract_name,
                "compiler_version": compiler_version,
                "contract_file": contract_file
            }
            
            return result
            
        except Exception as e:
            logger.error(f"error in get the contract's source code: {str(e)}")
            return None
        
    
    def get_slither_contract(self, contract_info):
        if not contract_info:
            return None
            
        try:
            compiler_version = contract_info.get("compiler_version", "")
            if not compiler_version:
                logger.error("No compiler version found in contract info")
                return None

            version = compiler_version.split("+")[0]
            
            install_cmd = f"solc-select install {version}"
            try:
                result = os.system(install_cmd)
                if result != 0:
                    logger.error(f"Failed to install solc version {version}")
                    return None
            except Exception as e:
                logger.error(f"Error installing solc version {version}: {str(e)}")
                return None
            
            use_cmd = f"solc-select use {version}"
            try:
                result = os.system(use_cmd)
                if result != 0:
                    logger.error(f"Failed to switch to solc version {version}")
                    return None
            except Exception as e:
                logger.error(f"Error switching to solc version {version}: {str(e)}")
                return None
            
            source_path = None
            if "contract_file" in contract_info:
                source_path = contract_info["contract_file"]
            elif "main_file" in contract_info and "contract_dir" in contract_info:
                source_path = os.path.join(contract_info["contract_dir"], contract_info["main_file"])
            
            if not source_path or not os.path.exists(source_path):
                logger.error(f"Source file not found: {source_path}")
                return None
            
            from slither.slither import Slither
            slither = Slither(source_path)
            
            contract_name = contract_info.get("contract_name")
            if not contract_name:
                logger.error("No contract name found in contract info")
                return None
                
            sli_contract = slither.get_contract_from_name(contract_name)[0]

            return sli_contract
            
        except Exception as e:
            logger.error(f"Error in get_slither_contract: {str(e)}")
            return None



# ==================================== test ============================================

def test_OnlineHelper():
    helper = OnlineHelper("bnb", -1)
    address = "0x55d398326f99059fF775485246999027B3197955"
    res = helper.get_contract_sourcecode(address)
    print(res)
    sli_contract = helper.get_slither_contract(res)
    print(sli_contract)
    for func in sli_contract.functions:
        print(func.canonical_name)
    return


if __name__ == "__main__":
    test_OnlineHelper()