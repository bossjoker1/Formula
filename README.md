# Formula Extractor

> With Symbolic Execution.

based on Slither

script:

```shell
python3 main.py -ch eth -t /home/bosi/bigfuzzer/formula/benchmark/AEST/AEST.sol AEST
```

## Usage

```bash

usage: main.py [-h] -m {offline,online} [-ch CHAIN] [-addr ADDRESSES [ADDRESSES ...]] [-b BLOCK]
               [-t PATH [NAME ...]] [-r] [--max_iter MAX_ITER]

options:
  -h, --help            show this help message and exit
  -m {offline,online}, --mode {offline,online}
                        Analysis mode: 'offline' requires all contract sources, 'online' allows chain
                        querying
  -ch CHAIN, --chain CHAIN
                        The chain to analyze (e.g., 'ethereum', 'bsc'). Required in online mode
  -addr ADDRESSES [ADDRESSES ...], --addresses ADDRESSES [ADDRESSES ...]
                        Contract addresses on chain. Required in online mode. Example: -addr addr1 addr2
                        addr3
  -b BLOCK, --block BLOCK
                        [Online mode only] Block number to analyze. If not specified, latest block will be
                        used
  -t PATH [NAME ...], --contracts PATH [NAME ...]
                        [Offline mode only] Specify all contract paths and their main contract names.
                        Example: -t path_1 contract_name_1 path_2 contract_name_2
  -r, --refined         refine the expression to get clearer results
  --max_iter MAX_ITER   maximum number of iterations


```

## TODO

so many todo...
