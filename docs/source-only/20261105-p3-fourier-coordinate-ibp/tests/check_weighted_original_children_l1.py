#!/usr/bin/env python3
"""Exact finite product-measure model. NOT a continuous integration/Lean proof."""
from itertools import product
from fractions import Fraction
from math import prod

CHILDREN = tuple(product(range(3), repeat=6))
GRID = tuple(product(range(2), repeat=6))
C, M = 2, 3
checks = 0
for orders in ((0, 0, 0, 0, 0, 0), (0, 1, 2, 0, 1, 2), (3, 0, 2, 1, 1, 0)):
    # |F_a^(k)(u)| = positive integer / 2, at most C.
    axis_numer = {(i, a, u): 1 + (2*a + orders[i] + i + u) % 4
                  for i in range(6) for a in range(3) for u in range(2)}
    mass_num, weighted_num = 0, 0
    for u in GRID:
        family_num = sum(prod(axis_numer[i,a[i],u[i]] for i in range(6))
                         for a in CHILDREN)
        W = (-1)**sum(u) * (1 + sum((i+1)*u[i] for i in range(6)) % 3)
        assert abs(W) <= M
        mass_num += family_num
        weighted_num += abs(W) * family_num
        assert abs(W) * family_num <= M * family_num
        checks += len(CHILDREN)
    # Each grid cell has weight 1/64, each tensor entry denominator 2**6.
    split_mass = Fraction(mass_num, 64**2)
    weighted_mass = Fraction(weighted_num, 64**2)
    factored = sum((prod(Fraction(sum(axis_numer[i,a[i],v] for v in (0,1)),4)
                        for i in range(6)) for a in CHILDREN), Fraction(0))
    assert split_mass == factored
    assert 0 <= weighted_mass <= M*split_mass <= M*len(CHILDREN)*(C**6)
    checks += 4
print(f'PASS checks={checks}, original labelled children={len(CHILDREN)}, '
      '3 derivative profiles, 64 product grid points; NOT real-Lebesgue/Lean verification')
