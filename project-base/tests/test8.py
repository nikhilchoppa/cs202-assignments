def power(base: int, exponent: int) -> int:
    if exponent == 0:
        return 1
    else:
        return base * power(base, exponent - 1)

print(power(2, 10))
