from web3 import Web3
from typing import Tuple

def sort_tokens(token_a: int, token_b: int) -> Tuple[str, str]:
    addr_a = Web3.to_checksum_address(hex(token_a))
    addr_b = Web3.to_checksum_address(hex(token_b))
    assert addr_a != addr_b, "IDENTICAL_ADDRESSES"
    assert addr_a != '0x0000000000000000000000000000000000000000', "ZERO_ADDRESS"
    assert addr_b != '0x0000000000000000000000000000000000000000', "ZERO_ADDRESS"
    if addr_a.lower() < addr_b.lower():
        return (addr_a, addr_b)
    return (addr_b, addr_a)


def PancakeRouter_get_pair_address(factory_address: int, token_a: int, token_b: int) -> str:
    w3 = Web3()
    factory = Web3.to_checksum_address(hex(factory_address))
    token0, token1 = sort_tokens(token_a, token_b)
    INIT_CODE_HASH = '0x00fb7f630766e6a796048ea87d01acd3068e8ff67d078148a3fa3f4a84f69bd5'
    salt = w3.solidity_keccak(['address', 'address'], [token0, token1])
    create2_input = w3.solidity_keccak(
        ['bytes1', 'address', 'bytes32', 'bytes32'],
        [b'\xff', factory, salt, INIT_CODE_HASH]
    )
    pair_address = '0x' + create2_input.hex()[-40:]
    return Web3.to_checksum_address(pair_address)


if __name__ == "__main__":
    factory = 0xcA143Ce32Fe78f1f7019d7d551a6402fC5350c73
    token_a = 0xbb4CdB9CBd36B01bD1cBaEBF2De08d9173bc095c
    token_b = 0xdDc0CFF76bcC0ee14c3e73aF630C029fe020F907
    
    pair_address = PancakeRouter_get_pair_address(factory, token_a, token_b)
    print(f"Pair address: {pair_address}")