# Template Record


## Pancake v2 

### Factory

- addr: 0xcA143Ce32Fe78f1f7019d7d551a6402fC5350c73 

- Pair和Router合约会调用`PairFor()`或者`createPair()`，来获得传入两个token的对应流动性池(Pair)的地址

- 所以只需要python脚本直接实现相同功能的solidity代码即可[pairFor.py](./scripts/pairFor.py)。√ 


### Pair

- addr: 基于传入的两个token地址通过`PairFor()`函数计算得到



### Router

- addr: 0x10ED43C718714eb63d5aA57B78B54704E256024E


### PancakeCallee

- `pancakeCall()`: 用户调用`swap()`or flashloan 后的回调函数。

---