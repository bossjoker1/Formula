import argparse
import sys
from loguru import logger
from Contract import BuildFormula, FContract
from typing import List
import config

# read args
# ================================================================

parser = argparse.ArgumentParser()

# 添加模式选择参数
parser.add_argument(
    "-m", "--mode",
    choices=["offline", "online"],
    required=True,
    help="Analysis mode: 'offline' requires all contract sources, 'online' allows chain querying"
)

# 链相关参数（在线模式必需）
parser.add_argument(
    "-ch", "--chain",
    help="The chain to analyze (e.g., 'ethereum', 'bsc'). Required in online mode",
)

parser.add_argument(
    "-addr", "--addresses",
    nargs="+",
    help="Contract addresses on chain. Required in online mode. Example: -addr addr1 addr2 addr3"
)

# 离线模式的合约参数
parser.add_argument(
    "-t", "--contracts",
    nargs="+",
    metavar=("PATH", "NAME"),
    help="[Offline mode only] Specify all contract paths and their main contract names. Example: -t path_1 contract_name_1 path_2 contract_name_2"
)

parser.add_argument(
    "-r", "--refined",
    action="store_true",
    help="refine the expression to get clearer results"
)

parser.add_argument(
    "--max_iter",
    type=int,
    default=100,
    help="maximum number of iterations"
)

args = parser.parse_args()


if args.mode == "online":
    if not args.chain or not args.addresses:
        parser.error("Online mode requires both --chain and --addresses arguments")
    if args.contracts:
        parser.error("Online mode does not accept --contracts argument, please use --addresses instead")
    contract_pairs = []
    chain_info = {
        "chain": args.chain,
        "addresses": args.addresses
    }
else:  # offline mode
    if not args.contracts:
        parser.error("Offline mode requires --contracts argument")
    if len(args.contracts) % 2 != 0:
        parser.error("Each contract path must be followed by the main contract name")
    contract_pairs = [(args.contracts[i], args.contracts[i + 1]) for i in range(0, len(args.contracts), 2)]
    chain_info = None

def testArgsParse():
    print(f"Mode: {args.mode}")
    if args.mode == "online":
        print(f"Chain: {args.chain}")
        print("Contract Addresses:")
        for addr in args.addresses:
            print(f"  - {addr}")
    else:
        print("Contracts:")
        for path, name in contract_pairs:
            print(f"  - Path: {path}, Name: {name}")

if __name__ == "__main__":
    # Update global config
    config.refined = args.refined
    config.max_iter = args.max_iter
    config.mode = args.mode
    config.chain_info = chain_info

    # set log level
    logger.add("./log", level="DEBUG")
    global analyzed_contracts
    analyzed_contracts: List[FContract] = []
    if contract_pairs:
        BuildFormula(contract_pairs)