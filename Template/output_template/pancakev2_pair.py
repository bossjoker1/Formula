from z3 import *


class PancakeV2Pair:
    def __init__(self):
        self.token0 = Int('token0')
        self.token1 = Int('token1')
        self.reserve0 = Int('reserve0')
        self.reserve1 = Int('reserve1')
        self.totalSupply = Int('totalSupply')

        

from z3 import *

def pancake_v2_pair_update():
    """分析_update函数中状态变量的变化"""
    
    # 定义z3变量
    balance0 = Int('balance0')
    balance1 = Int('balance1')
    _reserve0 = Int('_reserve0')
    _reserve1 = Int('_reserve1')
    blockTimestampLast_old = Int('blockTimestampLast_old')
    price0CumulativeLast_old = Int('price0CumulativeLast_old')
    price1CumulativeLast_old = Int('price1CumulativeLast_old')
    timestamp = Int('timestamp')
    timeElapsed = timestamp - blockTimestampLast_old

    expressions = {
        'reserve0': [
            balance0
        ],
        'reserve1': [
            balance1
        ],
        'blockTimestampLast': [
            timestamp
        ],
        'price0CumulativeLast': [
            # 当timeElapsed == 0 || _reserve0 == 0 || _reserve1 == 0时
            price0CumulativeLast_old,
            # 当timeElapsed > 0 && _reserve0 != 0 && _reserve1 != 0时
            price0CumulativeLast_old + (_reserve1 * timeElapsed) / _reserve0
        ],
        'price1CumulativeLast': [
            # 当timeElapsed == 0 || _reserve0 == 0 || _reserve1 == 0时
            price1CumulativeLast_old,
            # 当timeElapsed > 0 && _reserve0 != 0 && _reserve1 != 0时
            price1CumulativeLast_old + (_reserve0 * timeElapsed) / _reserve1
        ]
    }
    
    return expressions

def print_result_list(func, result):
    print("Function: ", func)
    for key, list in result.items():
        print(f"[S]  {key}:")
        for i, value in enumerate(list):
            print(f"{i}: {value}")
    print("="*100)

if __name__ == '__main__':
    result = pancake_v2_pair_update()
    print_result_list("pancake_v2_pair__update", result)
