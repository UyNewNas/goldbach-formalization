#!/usr/bin/env python3
"""Finite exact algebra regression for P3HBSmoothTensorL1 (not Lean/kernel proof).

A two-cell counting-measure surrogate checks six-axis product factorization
and summation over ALL 3**6 original child labels. It does not assert any
analytic equality for Lebesgue integrals or smoothness of the actual chi.
"""
from fractions import Fraction
from itertools import product
from math import prod


def toy_derivative(i: int, a: int, cell: int, k: int) -> Fraction:
    # Deliberately signed, child/order/axis-dependent exact test data.
    return Fraction((-1) ** (a + i + k) * (i + 1) * (a + 2) * (cell + 1) ** (k + 1),
                    (k + 1) * (a + 1))


def check(orders: tuple[int, ...]) -> int:
    labels = list(product(range(3), repeat=6))
    cells = list(product(range(2), repeat=6))
    axis_mass = [[sum((abs(toy_derivative(i, a, t, orders[i])) for t in range(2)), Fraction(0))
                  for a in range(3)] for i in range(6)]
    full_sum = sum((prod(abs(toy_derivative(i, child[i], cell[i], orders[i]))
                         for i in range(6))
                    for child in labels for cell in cells), Fraction(0))
    product_then_sum = sum((prod(axis_mass[i][child[i]] for i in range(6))
                            for child in labels), Fraction(0))
    child_then_product = prod(sum(axis_mass[i], Fraction(0)) for i in range(6))
    assert full_sum == product_then_sum == child_then_product
    return len(labels) * len(cells)


def main() -> None:
    orders_list = ((0, 0, 0, 0, 0, 0), (0, 1, 2, 0, 1, 2), (2, 2, 2, 2, 2, 2))
    total = sum(check(orders) for orders in orders_list)
    print(f"PASS: {len(orders_list)} exact scenarios; {total} original child/point pairs; "
          "six-axis factorizations, sum/integral interchange and child-label restoration")


if __name__ == "__main__":
    main()
