def sum_n(n: int) -> int:
    if n == 1:
        return 1
    else:
        return n + sum_n(n - 1)

print(sum_n(10))
