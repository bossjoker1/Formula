from z3 import *


class PancakeV2Pair:
    def __init__(self):
        self.reserve0 = Int('reserve0')
        self.reserve1 = Int('reserve1')
        self.price0CumulativeLast = Int('price0CumulativeLast')
        self.price1CumulativeLast = Int('price1CumulativeLast')
        self.blockTimestampLast = Int('blockTimestampLast')
        self.totalSupply = Int('totalSupply')


    def pancake_v2_pair__update(self):
        # 函数参数
        balance0 = Int('balance0')
        balance1 = Int('balance1')
        _reserve0 = Int('_reserve0')
        _reserve1 = Int('_reserve1')

        # 区块链原语
        block_timestamp = Int('block.timestamp')

        # 计算表达式
        result = {
            # reserve 更新
            'reserve0': balance0,
            'reserve1': balance1,
            'blockTimestampLast': block_timestamp,

            # price 累积值更新（条件更新写法）
            'price0CumulativeLast': If(
                And(block_timestamp - self.blockTimestampLast > 0, _reserve0 != 0, _reserve1 != 0),
                self.price0CumulativeLast + (_reserve1 * (block_timestamp - self.blockTimestampLast)) / _reserve0,
                self.price0CumulativeLast
            ),
            'price1CumulativeLast': If(
                And(block_timestamp - self.blockTimestampLast > 0, _reserve0 != 0, _reserve1 != 0),
                self.price1CumulativeLast + (_reserve0 * (block_timestamp - self.blockTimestampLast)) / _reserve1,
                self.price1CumulativeLast
            )
        }

        return result
    

    def pancake_v2_pair__mint(self):
        # 函数参数
        to = BitVec('to', 160)
        value = Int('value')

        # 状态变量（需声明）
        totalSupply = Int('totalSupply')
        balanceOf_to = Int('balanceOf[to]')

        # 计算表达式
        result = {
            'totalSupply': totalSupply + value,
            'balanceOf[to]': balanceOf_to + value
        }

        return result
    

    def pancake_v2_pair__mintFee(self):

        # 函数参数
        _reserve0 = Int('_reserve0')
        _reserve1 = Int('_reserve1')

        # 状态变量
        factory = BitVec('factory', 160)
        feeTo = BitVec('feeTo', 160)
        kLast = Int('kLast')
        totalSupply = Int('totalSupply')
        balanceOf_feeTo = Int('balanceOf[feeTo]')

        # sqrt 作为 uninterpreted function
        sqrt = Function('sqrt', IntSort(), IntSort())
        rootK = sqrt(_reserve0 * _reserve1)
        rootKLast = sqrt(kLast)

        # liquidity 表达式
        numerator = self.totalSupply * (rootK - rootKLast) * 8
        denominator = rootK * 17 + rootKLast * 8
        liquidity_expr = numerator / denominator

        # 条件构造
        feeOn = feeTo != BitVecVal(0, 160)
        cond_mint = And(
            feeOn,
            kLast != 0,
            rootK > rootKLast,
            liquidity_expr > 0
        )
        cond_klast_reset = And(Not(feeOn), kLast != 0)

        # 最终状态变量更新表达式
        result = {
            'totalSupply': If(cond_mint, self.totalSupply + liquidity_expr, self.totalSupply),
            'balanceOf[feeTo]': If(cond_mint, balanceOf_feeTo + liquidity_expr, balanceOf_feeTo),
            'kLast': If(cond_klast_reset, 0, kLast)
        }

        return result
    

    def pancake_v2_pair_mint(self):

        # 引入 sqrt 函数
        sqrt = Function('sqrt', IntSort(), IntSort())

        # 状态变量
        reserve0 = Int('reserve0')
        reserve1 = Int('reserve1')
        blockTimestampLast = Int('blockTimestampLast')
        price0CumulativeLast = Int('price0CumulativeLast')
        price1CumulativeLast = Int('price1CumulativeLast')
        totalSupply = Int('totalSupply')
        kLast = Int('kLast')
        balanceOf_to = Int('balanceOf[to]')
        balanceOf_0 = Int('balanceOf[address(0)]')
        balanceOf_feeTo = Int('balanceOf[feeTo]')

        # 区块链状态
        block_timestamp = Int('block.timestamp')
        token0_balance = Int('token0.balanceOf[this]')
        token1_balance = Int('token1.balanceOf[this]')
        MINIMUM_LIQUIDITY = IntVal(10**3)

        # 局部变量（通过表达式建模）
        _reserve0 = reserve0
        _reserve1 = reserve1
        amount0 = token0_balance - _reserve0
        amount1 = token1_balance - _reserve1

        # 预生成：_mintFee 的影响
        rootK = sqrt(_reserve0 * _reserve1)
        rootKLast = sqrt(kLast)
        liquidity_fee = (totalSupply * (rootK - rootKLast) * 8) / (rootK * 17 + rootKLast * 8)

        # _mintFee 的表达式对状态变量的影响（参考 internal 函数分析）
        base_totalSupply_exprs = [
            totalSupply,  # 无影响
            totalSupply + liquidity_fee
        ]
        base_balanceOf_feeTo_exprs = [
            balanceOf_feeTo + liquidity_fee
        ]

        # _mint 的两种路径
        liquidity_case0 = sqrt(amount0 * amount1) - MINIMUM_LIQUIDITY
        liquidity_case1_op1 = (amount0 * totalSupply) / _reserve0
        liquidity_case1_op2 = (amount1 * totalSupply) / _reserve1

        # _update 的状态更新
        price0_add = (_reserve1 * (block_timestamp - blockTimestampLast)) / _reserve0
        price1_add = (_reserve0 * (block_timestamp - blockTimestampLast)) / _reserve1

        # reserve 变更来自 balance
        reserve0_new = token0_balance
        reserve1_new = token1_balance

        # kLast 更新
        kLast_new = token0_balance * token1_balance

        # === 汇总状态变量最终表达式列表 ===
        result = {
            'totalSupply': [],
            'balanceOf[to]': [],
            'balanceOf[address(0)]': [],
            'balanceOf[feeTo]': base_balanceOf_feeTo_exprs,
            'reserve0': [reserve0_new],
            'reserve1': [reserve1_new],
            'blockTimestampLast': [block_timestamp],
            'price0CumulativeLast': [
                price0CumulativeLast + price0_add
            ],
            'price1CumulativeLast': [
                price1CumulativeLast + price1_add
            ],
            'kLast': [kLast_new],
            # 额外跟踪 ERC20 合约的状态变化
            'token0.balanceOf[this]': [token0_balance - liquidity_case0],
            'token1.balanceOf[this]': [token1_balance - liquidity_case0],
            'token0.balanceOf[to]': [liquidity_case0],
            'token1.balanceOf[to]': [liquidity_case0]
        }

        # 合成 totalSupply 表达式列表
        for ts in base_totalSupply_exprs:
            result['totalSupply'].append(ts + simplify(liquidity_case0) + MINIMUM_LIQUIDITY)
            result['totalSupply'].append(ts + simplify(liquidity_case1_op1))
            result['totalSupply'].append(ts + simplify(liquidity_case1_op2))

        # balanceOf[to]
        result['balanceOf[to]'].append(balanceOf_to + simplify(liquidity_case0))
        result['balanceOf[to]'].append(balanceOf_to + simplify(liquidity_case1_op1))
        result['balanceOf[to]'].append(balanceOf_to + simplify(liquidity_case1_op2))

        # balanceOf[address(0)] 只可能在 case0 中出现
        result['balanceOf[address(0)]'].append(balanceOf_0 + MINIMUM_LIQUIDITY)

        return result
    

    def pancake_v2_pair_burn(self):

        # 引入 sqrt 函数
        sqrt = Function('sqrt', IntSort(), IntSort())

        # 状态变量
        reserve0 = Int('reserve0')
        reserve1 = Int('reserve1')
        blockTimestampLast = Int('blockTimestampLast')
        price0CumulativeLast = Int('price0CumulativeLast')
        price1CumulativeLast = Int('price1CumulativeLast')
        totalSupply = Int('totalSupply')
        balanceOf_this = Int('balanceOf[address(this)]')
        balanceOf_feeTo = Int('balanceOf[feeTo]')
        kLast = Int('kLast')

        # 链上原语 & 传入数据
        token0_balance = Int('token0.balanceOf[this]')
        token1_balance = Int('token1.balanceOf[this]')
        block_timestamp = Int('block.timestamp')

        _reserve0 = reserve0
        _reserve1 = reserve1

        # _mintFee 的影响
        rootK = sqrt(_reserve0 * _reserve1)
        rootKLast = sqrt(kLast)
        liquidity_fee = (totalSupply * (rootK - rootKLast) * 8) / (rootK * 17 + rootKLast * 8)

        base_totalSupply_exprs = [
            totalSupply,                         # 没触发 _mintFee
            totalSupply + liquidity_fee          # 触发 _mintFee
        ]
        base_balanceOf_feeTo_exprs = [
            balanceOf_feeTo + liquidity_fee      # 触发 _mintFee
        ]

        # 传递到 _burn(address(this), liquidity)
        # liquidity = balanceOf[address(this)]
        liquidity = balanceOf_this

        # amount0/1 = liquidity * token_balance / totalSupply
        amount0_exprs = [(liquidity * token0_balance) / ts for ts in base_totalSupply_exprs]
        amount1_exprs = [(liquidity * token1_balance) / ts for ts in base_totalSupply_exprs]

        # 最终总表达式
        result = {
            'totalSupply': [],
            'balanceOf[address(this)]': [],
            'balanceOf[feeTo]': base_balanceOf_feeTo_exprs,
            'reserve0': [token0_balance],
            'reserve1': [token1_balance],
            'blockTimestampLast': [block_timestamp],
            'price0CumulativeLast': [
                price0CumulativeLast + (_reserve1 * (block_timestamp - blockTimestampLast)) / _reserve0
            ],
            'price1CumulativeLast': [
                price1CumulativeLast + (_reserve0 * (block_timestamp - blockTimestampLast)) / _reserve1
            ],
            'kLast': [token0_balance * token1_balance],
            # 额外跟踪 ERC20 合约的状态变化
            'token0.balanceOf[this]': [token0_balance - liquidity],
            'token1.balanceOf[this]': [token1_balance - liquidity],
            'token0.balanceOf[to]': [amount0_exprs],
            'token1.balanceOf[to]': [amount1_exprs]
        }

        # 将 _burn 的结果（减少）叠加到 _mintFee 的 totalSupply 结果上
        for ts in base_totalSupply_exprs:
            result['totalSupply'].append(ts - liquidity)

        # balanceOf[address(this)] -= liquidity
        result['balanceOf[address(this)]'].append(balanceOf_this - liquidity)

        return result





def print_result(func, result):
    print("Function: ", func)
    for key, value in result.items():
        print(f"{key}: {value}")
    print("-"*100)

def print_result_list(func, result):
    print("Function: ", func)
    for key, list in result.items():
        print(f"[S]  {key}:")
        for i, value in enumerate(list):
            print(f"{i}: {value}")
    print("-"*100)


if __name__ == '__main__':
    pair = PancakeV2Pair()
    print_result("pancake_v2_pair__update", pair.pancake_v2_pair__update())
    print_result("pancake_v2_pair__mint", pair.pancake_v2_pair__mint())
    print_result("pancake_v2_pair__mintFee", pair.pancake_v2_pair__mintFee())
    print_result_list("pancake_v2_pair_mint", pair.pancake_v2_pair_mint())
    print_result_list("pancake_v2_pair_burn", pair.pancake_v2_pair_burn())