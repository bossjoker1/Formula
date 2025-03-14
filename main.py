import argparse
import sys
from loguru import logger
from Contract import BuildFormula, FContract
from typing import List

# read args
# ================================================================

parser = argparse.ArgumentParser()

parser.add_argument(
    "-ch", "--chain", help="The chain to which the contract is deployed"
)

parser.add_argument(
    "-t", "--contracts",
    nargs="+",
    metavar=("PATH", "NAME"),
    help="Specify contract paths and their main contract names. Example: -t path_1 contract_name_1 path_2 contract_name_2"
)

parser.add_argument(
    "-r", "--refined",
    action="store_true",
    help="refine the expression to get clearer results"
)


args = parser.parse_args()


if args.contracts:
    if len(args.contracts) % 2 != 0:
        parser.error("Each contract path must be followed by the main contract name.")
    
    contract_pairs = [(args.contracts[i], args.contracts[i + 1]) for i in range(0, len(args.contracts), 2)]
else:
    contract_pairs = []


def testArgsParse():
    print("Chain:", args.chain)
    print("Contracts:")
    for path, name in contract_pairs:
        print(f"  - Path: {path}, Name: {name}")


if __name__ == "__main__":

    # set log level
    logger.add("./log", level="DEBUG")
    global analyzed_contracts
    analyzed_contracts: List[FContract] = []
    if  contract_pairs:
        BuildFormula(contract_pairs, args.refined)