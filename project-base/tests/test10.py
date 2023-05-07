def sum_of_natural_numbers(n: int) -> int:
    if n == 0:
        return 0
    else:
        return n + sum_of_natural_numbers(n - 1)

print(sum_of_natural_numbers(10))
