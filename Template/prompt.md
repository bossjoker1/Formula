# Prompt Design

AEST:

AEST: 0xdDc0CFF76bcC0ee14c3e73aF630C029fe020F907
bnb : 0xbb4CdB9CBd36B01bD1cBaEBF2De08d9173bc095c
router: 0x10ED43C718714eb63d5aA57B78B54704E256024E
pair: 0xff12EaA67E9208ff795B172129452BA399fa4BE0
factory: 0xcA143Ce32Fe78f1f7019d7d551a6402fC5350c73


```python
// returns sorted token addresses, used to handle return values from pairs sorted in this order
    function sortTokens(address tokenA, address tokenB) internal pure returns (address token0, address token1) {
        require(tokenA != tokenB, 'PancakeLibrary: IDENTICAL_ADDRESSES');
        (token0, token1) = tokenA < tokenB ? (tokenA, tokenB) : (tokenB, tokenA);
        require(token0 != address(0), 'PancakeLibrary: ZERO_ADDRESS');
    }

    // calculates the CREATE2 address for a pair without making any external calls
    function pairFor(address factory, address tokenA, address tokenB) internal pure returns (address pair) {
        (address token0, address token1) = sortTokens(tokenA, tokenB);
        pair = address(uint(keccak256(abi.encodePacked(
                hex'ff',
                factory,
                keccak256(abi.encodePacked(token0, token1)),
                hex'00fb7f630766e6a796048ea87d01acd3068e8ff67d078148a3fa3f4a84f69bd5' // init code hash
            ))));
    }
```
这是bnb pancake router合约的library的部分代码，上面的pairFor函数可以转化为直接用python代码实现，函数传参为两个token地址(python 16进制Int型)，然后返回得到的Pair地址。请帮我实现。



我目前用python基于Slither和z3编写了一个提取合约的public函数对所有状态变量的计算表达式的静态符号执行工具，这里的状态变量可以是被分析合约(后面成为合约A)的状态变量，也可以是合约A的public函数跨合约调用其它合约，并影响其它合约的状态变量，即所有被影响合约构成的集合的状态变量的计算表达式。目前对于一些中等大小的合约函数，可以有精确的效果。
如对于AEST合约函数distributeFee():
```solidity
function distributeFee() public {
        uint256 mokeyFeeTotal = swapFeeTotal.mul(2);
        super._transfer(uniswapV2Pair, monkeyWallet, mokeyFeeTotal);
        super._transfer(uniswapV2Pair, birdWallet, swapFeeTotal);
        super._transfer(uniswapV2Pair, foundationWallet, swapFeeTotal);
        super._transfer(uniswapV2Pair, technologyWallet, swapFeeTotal);
        super._transfer(uniswapV2Pair, marketingWallet, swapFeeTotal);
        swapFeeTotal = 0;
    }
```
可以提取得到如下的表达式(示例不是完整的)：
```Ocaml
StateVar: _balances[birdWallet] in function AEST.distributeFee(), formula: 
Expression [0]: _balances[birdWallet] + swapFeeTotal, 
Constraint [0]: And(_balances[uniswapV2Pair] >= 2*swapFeeTotal,
    Not(monkeyWallet == 0),
    Not(uniswapV2Pair == 0),
    _balances[uniswapV2Pair] + -3*swapFeeTotal >= 0,
    Not(birdWallet == 0),
    _balances[uniswapV2Pair] + -4*swapFeeTotal >= 0,
    Not(foundationWallet == 0),
    _balances[uniswapV2Pair] + -5*swapFeeTotal >= 0,
    Not(technologyWallet == 0),
    _balances[uniswapV2Pair] + -6*swapFeeTotal >= 0,
    Not(marketingWallet == 0))
```

但是对于比较复杂的，如BNB链上的Pancake Router合约(0x10ED43C718714eb63d5aA57B78B54704E256024E)，包含与Pancake Factory(0xcA143Ce32Fe78f1f7019d7d551a6402fC5350c73)进行交互。然而，Router, Pair以及Factory合约都是比较固定的，而且更新速度较慢，因此有一个很好的想法是将这些合约的计算表达式直接手动提取出来作为模板。该步骤我需要借助你作为大模型的功能来帮助我完成。

你先知晓我的任务，不用输出，我会继续引导你。


---

首先，我们处理Pancake Pair合约，它自己的合约本身包含的public状态变量为以下部分：
solidity
address public factory;
address public token0; 
address public token1; 

uint112 private reserve0;  
uint112 private reserve1;  

uint public price0CumulativeLast; 
uint public price1CumulativeLast; 
uint public kLast; // reserve0 * reserve1, as of immediately after the most recent liquidity event

虽然我们关注的是external(public)函数，但我们先从internal function 出发会方便后续的分析。
请给出状态变量的计算表达式，注意必须是以下形式：
sV = Op * V  ， 其中sV是状态变量，V属于状态变量或者函数传参。
然后等式右边需要转为z3.ExprRef, 即z3表达式，所以你需要生成一个python程序。
注意uint256, uint112均直接是z3 int类型，address就是BitVec(160)，另外bool和string就对应z3的类型。
这是进一步的要求，你不需要输出，后面我将给你具体的函数去分析然后根据你的结果进行调整。

---

首先是 `_update()`函数
```solidity
function _update(uint balance0, uint balance1, uint112 _reserve0, uint112 _reserve1) private {
        require(balance0 <= uint112(-1) && balance1 <= uint112(-1), 'Pancake: OVERFLOW');
        uint32 blockTimestamp = uint32(block.timestamp % 2**32);
        uint32 timeElapsed = blockTimestamp - blockTimestampLast; // overflow is desired
        if (timeElapsed > 0 && _reserve0 != 0 && _reserve1 != 0) {
            // * never overflows, and + overflow is desired
            price0CumulativeLast += uint(UQ112x112.encode(_reserve1).uqdiv(_reserve0)) * timeElapsed;
            price1CumulativeLast += uint(UQ112x112.encode(_reserve0).uqdiv(_reserve1)) * timeElapsed;
        }
        reserve0 = uint112(balance0);
        reserve1 = uint112(balance1);
        blockTimestampLast = blockTimestamp;
        emit Sync(reserve0, reserve1);
    }
```

---
ok, 整体结果不错，但是有点问题，
一个是输出结果：
reserve0: 就直接是balance0了
其他的也是。
另外输出有：
```
price0CumulativeLast: price0CumulativeLast ==
If(And(timeElapsed > 0, _reserve0 != 0, _reserve1 != 0),
   price0CumulativeLast + (_reserve1*timeElapsed)/_reserve0,
   price0CumulativeLast)
```
你做的好的点是，忽略了UQ112x112引入的额外的操作，然而timeElapsed并不是函数参数，也不是状态变量，这不符合我给的计算表达式的定义。我更新一下等式右边的变量还可以是block.timestamp这些区块链自带的变量。同时你同样需要忽略%2**32这种额外操作。
所以你需要重新生成一下，另外我需要你将代码放入到pancake_v2_pair__update这个python函数中

---

我修改上面的代码如下，我将状态变量作为class的变量了

```python
class PancakeV2Pair:
    def __init__(self):
        self.reserve0 = Int('reserve0')
        self.reserve1 = Int('reserve1')
        self.price0CumulativeLast = Int('price0CumulativeLast')
        self.price1CumulativeLast = Int('price1CumulativeLast')
        self.blockTimestampLast = Int('blockTimestampLast')

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

```
后面我让你分析新的函数你只需要往这个类里面加对应的Python函数即可。
你知道要求即可，本次不需要输出。


---

这是_mint的结果:
{'totalSupply': totalSupply + value, 'balanceOf[to]': balanceOf[to] + value}

现在需要分析_mintFee()函数，同样的要求：
```solidity
function _mintFee(uint112 _reserve0, uint112 _reserve1) private returns (bool feeOn) {
        address feeTo = IPancakeFactory(factory).feeTo();
        feeOn = feeTo != address(0);
        uint _kLast = kLast; // gas savings
        if (feeOn) {
            if (_kLast != 0) {
                uint rootK = Math.sqrt(uint(_reserve0).mul(_reserve1));
                uint rootKLast = Math.sqrt(_kLast);
                if (rootK > rootKLast) {
                    uint numerator = totalSupply.mul(rootK.sub(rootKLast)).mul(8);
                    uint denominator = rootK.mul(17).add(rootKLast.mul(8));
                    uint liquidity = numerator / denominator;
                    if (liquidity > 0) _mint(feeTo, liquidity);
                }
            }
        } else if (_kLast != 0) {
            kLast = 0;
        }
    }
```
注意此时引入一个新的问题，就是_mintFee调用了_mint函数，_mint的参数将由_mintFee传递得到，其计算表达式也会传进去进一步影响，你可以根据我得到的_mint函数的结果来辅助你生成_mintFee函数的表达式。

---

有问题，这里的liquidity需要得到它是怎么计算得来的，然后作为参数传递进去，而且Math.sqrt这里不能忽略，之前能忽略是因为做的操作是精度检查相关的。最后得到的liquidity应该是由_reserve0/1， KLast得到的

---


```python

def concretize_expr(expr, values: dict):
    """
    用 values 中的值替换 expr 里的变量，并把 sqrt(...) 替换成 math.isqrt(...)
    这个例子假设你手动展开 expr
    """
    _reserve0 = values['_reserve0']
    _reserve1 = values['_reserve1']
    kLast = values['kLast']
    totalSupply = values['totalSupply']

    rootK = math.isqrt(_reserve0 * _reserve1)
    rootKLast = math.isqrt(kLast)

    numerator = totalSupply * (rootK - rootKLast) * 8
    denominator = rootK * 17 + rootKLast * 8

    liquidity = numerator // denominator
    return liquidity

val = concretize_expr({
    '_reserve0': 9,
    '_reserve1': 4,
    'kLast': 16,
    'totalSupply': 1000
})
print(val)  # 输出 liquidity 的值
```

---

internal function已经处理完毕，它包含较少的跨函数调用，因此比较好分析。
下面，我们需要分析external/public函数，它会包含更多的分支和更多的跨函数调用。
但是由于我们是循序渐进的，已经获得了internal function的处理表达式，所以我觉得应该只需要带入参数就行。
考虑到状态变量可能会涉及到很多个表达式(分支)，所以对于external/public函数，我建议不要用If了，而是对应一个列表，
包含表达式和约束。
参考我之前的结果：
```
Expression [0]: _balances[birdWallet] + swapFeeTotal, 
Constraint [0]: And(_balances[uniswapV2Pair] >= 2*swapFeeTotal,
    Not(monkeyWallet == 0),
    Not(uniswapV2Pair == 0))
```
你不需要考虑约束是否有解，后面我会运行程序遍历整个列表来判断是否有解。
当前对话，你只需要知道我的引导和要求就行了。

---

分析


2025-03-28 10:16:56.556 | DEBUG    | Contract:OnlineBuild:68 - [F] function name:  PancakeERC20.constructor()
2025-03-28 10:16:56.557 | DEBUG    | Contract:OnlineBuild:68 - [F] function name:  PancakeERC20._mint(address,uint256)
2025-03-28 10:16:56.557 | DEBUG    | Contract:OnlineBuild:68 - [F] function name:  PancakeERC20._burn(address,uint256)
2025-03-28 10:16:56.557 | DEBUG    | Contract:OnlineBuild:68 - [F] function name:  PancakeERC20._approve(address,address,uint256)
2025-03-28 10:16:56.557 | DEBUG    | Contract:OnlineBuild:68 - [F] function name:  PancakeERC20._transfer(address,address,uint256)
2025-03-28 10:16:56.557 | DEBUG    | Contract:OnlineBuild:68 - [F] function name:  PancakeERC20.approve(address,uint256)
2025-03-28 10:16:56.557 | DEBUG    | Contract:OnlineBuild:68 - [F] function name:  PancakeERC20.transfer(address,uint256)
2025-03-28 10:16:56.557 | DEBUG    | Contract:OnlineBuild:68 - [F] function name:  PancakeERC20.transferFrom(address,address,uint256)
2025-03-28 10:16:56.557 | DEBUG    | Contract:OnlineBuild:68 - [F] function name:  PancakeERC20.permit(address,address,uint256,uint256,uint8,bytes32,bytes32)
2025-03-28 10:16:56.557 | DEBUG    | Contract:OnlineBuild:68 - [F] function name:  IPancakeERC20.name()
2025-03-28 10:16:56.557 | DEBUG    | Contract:OnlineBuild:68 - [F] function name:  IPancakeERC20.symbol()
2025-03-28 10:16:56.557 | DEBUG    | Contract:OnlineBuild:68 - [F] function name:  IPancakeERC20.decimals()
2025-03-28 10:16:56.557 | DEBUG    | Contract:OnlineBuild:68 - [F] function name:  IPancakeERC20.totalSupply()
2025-03-28 10:16:56.557 | DEBUG    | Contract:OnlineBuild:68 - [F] function name:  IPancakeERC20.balanceOf(address)
2025-03-28 10:16:56.557 | DEBUG    | Contract:OnlineBuild:68 - [F] function name:  IPancakeERC20.allowance(address,address)
2025-03-28 10:16:56.557 | DEBUG    | Contract:OnlineBuild:68 - [F] function name:  IPancakeERC20.approve(address,uint256)
2025-03-28 10:16:56.557 | DEBUG    | Contract:OnlineBuild:68 - [F] function name:  IPancakeERC20.transfer(address,uint256)
2025-03-28 10:16:56.557 | DEBUG    | Contract:OnlineBuild:68 - [F] function name:  IPancakeERC20.transferFrom(address,address,uint256)
2025-03-28 10:16:56.557 | DEBUG    | Contract:OnlineBuild:68 - [F] function name:  IPancakeERC20.DOMAIN_SEPARATOR()
2025-03-28 10:16:56.557 | DEBUG    | Contract:OnlineBuild:68 - [F] function name:  IPancakeERC20.PERMIT_TYPEHASH()
2025-03-28 10:16:56.557 | DEBUG    | Contract:OnlineBuild:68 - [F] function name:  IPancakeERC20.nonces(address)
2025-03-28 10:16:56.557 | DEBUG    | Contract:OnlineBuild:68 - [F] function name:  IPancakeERC20.permit(address,address,uint256,uint256,uint8,bytes32,bytes32)
2025-03-28 10:16:56.558 | DEBUG    | Contract:OnlineBuild:68 - [F] function name:  IPancakePair.name()
2025-03-28 10:16:56.558 | DEBUG    | Contract:OnlineBuild:68 - [F] function name:  IPancakePair.symbol()
2025-03-28 10:16:56.558 | DEBUG    | Contract:OnlineBuild:68 - [F] function name:  IPancakePair.decimals()
2025-03-28 10:16:56.558 | DEBUG    | Contract:OnlineBuild:68 - [F] function name:  IPancakePair.totalSupply()
2025-03-28 10:16:56.558 | DEBUG    | Contract:OnlineBuild:68 - [F] function name:  IPancakePair.balanceOf(address)
2025-03-28 10:16:56.558 | DEBUG    | Contract:OnlineBuild:68 - [F] function name:  IPancakePair.allowance(address,address)
2025-03-28 10:16:56.558 | DEBUG    | Contract:OnlineBuild:68 - [F] function name:  IPancakePair.approve(address,uint256)
2025-03-28 10:16:56.558 | DEBUG    | Contract:OnlineBuild:68 - [F] function name:  IPancakePair.transfer(address,uint256)
2025-03-28 10:16:56.558 | DEBUG    | Contract:OnlineBuild:68 - [F] function name:  IPancakePair.transferFrom(address,address,uint256)
2025-03-28 10:16:56.558 | DEBUG    | Contract:OnlineBuild:68 - [F] function name:  IPancakePair.DOMAIN_SEPARATOR()
2025-03-28 10:16:56.558 | DEBUG    | Contract:OnlineBuild:68 - [F] function name:  IPancakePair.PERMIT_TYPEHASH()
2025-03-28 10:16:56.558 | DEBUG    | Contract:OnlineBuild:68 - [F] function name:  IPancakePair.nonces(address)
2025-03-28 10:16:56.558 | DEBUG    | Contract:OnlineBuild:68 - [F] function name:  IPancakePair.permit(address,address,uint256,uint256,uint8,bytes32,bytes32)
2025-03-28 10:16:56.558 | DEBUG    | Contract:OnlineBuild:68 - [F] function name:  IPancakePair.MINIMUM_LIQUIDITY()
2025-03-28 10:16:56.558 | DEBUG    | Contract:OnlineBuild:68 - [F] function name:  IPancakePair.factory()
2025-03-28 10:16:56.558 | DEBUG    | Contract:OnlineBuild:68 - [F] function name:  IPancakePair.token0()
2025-03-28 10:16:56.558 | DEBUG    | Contract:OnlineBuild:68 - [F] function name:  IPancakePair.token1()
2025-03-28 10:16:56.558 | DEBUG    | Contract:OnlineBuild:68 - [F] function name:  IPancakePair.getReserves()
2025-03-28 10:16:56.558 | DEBUG    | Contract:OnlineBuild:68 - [F] function name:  IPancakePair.price0CumulativeLast()
2025-03-28 10:16:56.558 | DEBUG    | Contract:OnlineBuild:68 - [F] function name:  IPancakePair.price1CumulativeLast()
2025-03-28 10:16:56.558 | DEBUG    | Contract:OnlineBuild:68 - [F] function name:  IPancakePair.kLast()
2025-03-28 10:16:56.559 | DEBUG    | Contract:OnlineBuild:68 - [F] function name:  IPancakePair.mint(address)
2025-03-28 10:16:56.559 | DEBUG    | Contract:OnlineBuild:68 - [F] function name:  IPancakePair.burn(address)
2025-03-28 10:16:56.559 | DEBUG    | Contract:OnlineBuild:68 - [F] function name:  IPancakePair.swap(uint256,uint256,address,bytes)
2025-03-28 10:16:56.559 | DEBUG    | Contract:OnlineBuild:68 - [F] function name:  IPancakePair.skim(address)
2025-03-28 10:16:56.559 | DEBUG    | Contract:OnlineBuild:68 - [F] function name:  IPancakePair.sync()
2025-03-28 10:16:56.559 | DEBUG    | Contract:OnlineBuild:68 - [F] function name:  IPancakePair.initialize(address,address)
2025-03-28 10:16:56.559 | DEBUG    | Contract:OnlineBuild:68 - [F] function name:  PancakePair.getReserves()
2025-03-28 10:16:56.559 | DEBUG    | Contract:OnlineBuild:68 - [F] function name:  PancakePair._safeTransfer(address,address,uint256)
2025-03-28 10:16:56.559 | DEBUG    | Contract:OnlineBuild:68 - [F] function name:  PancakePair.constructor()
2025-03-28 10:16:56.559 | DEBUG    | Contract:OnlineBuild:68 - [F] function name:  PancakePair.initialize(address,address)
2025-03-28 10:16:56.559 | DEBUG    | Contract:OnlineBuild:68 - [F] function name:  PancakePair._update(uint256,uint256,uint112,uint112)
2025-03-28 10:16:56.559 | DEBUG    | Contract:OnlineBuild:68 - [F] function name:  PancakePair._mintFee(uint112,uint112)
2025-03-28 10:16:56.559 | DEBUG    | Contract:OnlineBuild:68 - [F] function name:  PancakePair.mint(address)
2025-03-28 10:16:56.559 | DEBUG    | Contract:OnlineBuild:68 - [F] function name:  PancakePair.burn(address)
2025-03-28 10:16:56.559 | DEBUG    | Contract:OnlineBuild:68 - [F] function name:  PancakePair.swap(uint256,uint256,address,bytes)
2025-03-28 10:16:56.559 | DEBUG    | Contract:OnlineBuild:68 - [F] function name:  PancakePair.skim(address)
2025-03-28 10:16:56.559 | DEBUG    | Contract:OnlineBuild:68 - [F] function name:  PancakePair.sync()
2025-03-28 10:16:56.559 | DEBUG    | Contract:OnlineBuild:68 - [F] function name:  PancakePair.slitherConstructorVariables()
2025-03-28 10:16:56.559 | DEBUG    | Contract:OnlineBuild:68 - [F] function name:  PancakePair.slitherConstructorConstantVariables()


我现在在做fuzzing 智能合约，找到其中的价格操纵漏洞，这类漏洞与传统的如重入或整数溢出漏洞不同，它通常需要多比交易才能触发。因此首先筛选出更可能触发该漏洞的函数作为candidates是必要的，我们定义的标准是它们针对reserve，totalsupply, allowance[], balanceOf[]的写操作，越多说明优先级越高。另外我们只考虑普通用户可以调用的public函数，因此如onlyowner修饰的函数也不考虑。我会跟你提供AEST，Pair和Router合约的代码，我需要你对它们进行排序。
具体来说，我希望你得到