#!/usr/bin/env python3
"""Independent finite exact-rational regression for the P3.6 integrated W/HB
Leibniz ledger. The polynomial H is a surrogate compact bump, NOT Lean
smoothTransition or a check of kernel acceptance."""
from itertools import product
from random import Random
import sympy as sp

rng = Random(3605)
x = sp.symbols('x0 x1')
cases = 0
points_per_dim = [sp.Rational(v, 2) for v in range(-3, 4)]
for d in (1, 2):
    variables = x[:d]
    for q in range(5):
        for repeat in range(9):
            coeff = [rng.randrange(-3, 4) for _ in range(2*d+1)]
            W = 1 + sum(coeff[k]*variables[k % d]**(1+(k//d))
                        for k in range(2*d+1))
            H = sp.prod((4-y*y)**6 for y in variables)
            iseq = tuple(rng.randrange(d) for _ in range(q))
            def jet(f, axes):
                z = f
                for idx in axes:
                    z = sp.diff(z, variables[idx])
                return sp.expand(z)
            actual = jet(W*H, iseq)
            split_sum = 0
            for bits in product((0, 1), repeat=q):
                ia = tuple(idx for idx, bit in zip(iseq, bits) if not bit)
                ib = tuple(idx for idx, bit in zip(iseq, bits) if bit)
                split_sum += jet(W, ia)*jet(H, ib)
            assert sp.expand(actual-split_sum) == 0
            test_points = list(product(points_per_dim, repeat=d))
            def vals(expr):
                fn = sp.lambdify(variables, expr, 'sympy')
                return [sp.Rational(fn(*point)) for point in test_points]
            left = sum(map(abs, vals(actual)))
            m = max(sum(map(abs, vals(jet(W, seq))))
                    for r in range(q+1)
                    for seq in product(range(d), repeat=r))
            b = max(max(map(abs, vals(jet(H, seq))))
                    for r in range(q+1)
                    for seq in product(range(d), repeat=r))
            assert left <= (2**q)*b*m
            cases += 1
print(f'PASS {cases}/{cases} exact polynomial Leibniz '
      'and rational-grid integrated majorant cases')
