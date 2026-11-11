#!/usr/bin/env python3
"""Finite exact rational sanity checks for TRUE one-step original-group product.
Uses polynomial Euler proxies, NOT the C-infinity cutoff, Lean or a kernel.
Includes empty products, equal group subsets with different positive scales,
strictly missing axes and repeated physical group occurrences.
"""
from fractions import Fraction
import sympy as S
x = S.symbols('x0:6')
t = S.symbols('t')
chi = 1 + t - t*t/S.Integer(3) + t**3/S.Integer(5)
psi = S.expand(chi - chi.subs(t, 2*t))
families = [
    ([], []),
    ([()], [S.Rational(1, 3)]),
    ([(0, 1)], [S.Rational(2, 3)]),
    ([(0, 1), (0, 1)], [S.Rational(2, 3), S.Rational(7, 5)]),
    ([(0, 1), (1, 2), (0, 1)], [S.Rational(2, 3), S.Rational(5, 4), S.Rational(3, 2)]),
    ([(0,), (1,), (2,), (3,)], [S.Rational(1, 3), S.Rational(2, 3), S.Rational(3, 4), S.Rational(4, 5)]),
]
points = [
    {xx: S.Rational(1 + (i % 3), 2 + (i % 2)) for i, xx in enumerate(x)},
    {xx: S.Rational(2 + (i % 2), 3 + (i % 3)) for i, xx in enumerate(x)},
    {xx: S.Rational(1 + (i % 2), 5 + (i % 3)) for i, xx in enumerate(x)},
]
count_exact = count_triangle = count_budget = 0
for groups, scales in families:
    assert len(groups) == len(scales)
    Fs = []
    for J, c in zip(groups, scales):
        mon = c
        for idx in J:
            mon *= x[idx]
        Fs.append(S.expand(psi.subs(t, mon)))
    g = len(Fs)
    for i in range(6):
        whole = S.prod(Fs)
        lhs = S.expand(x[i] * S.diff(whole, x[i]))
        derivatives = [S.expand(x[i] * S.diff(f, x[i])) for f in Fs]
        rhs = S.expand(sum((S.prod(Fs[:j]+Fs[j+1:]) * derivatives[j]
                             for j in range(g)), S.Integer(0)))
        assert S.expand(lhs-rhs) == 0, (groups, i)
        count_exact += 1
        for u in points:
            actual = S.Abs(lhs.subs(u))
            mass = sum((S.prod([S.Abs(f.subs(u)) for k,f in enumerate(Fs) if k != j])
                        *S.Abs(derivatives[j].subs(u)) for j in range(g)), S.Integer(0))
            assert actual <= mass, (groups, i, u)
            count_triangle += 1
            norms = [S.Abs(f.subs(u)) for f in Fs]+[S.Abs(d.subs(u)) for d in derivatives]
            C = max([S.Rational(1, 6)] + [z / 3 for z in norms])
            major = S.Integer(g) * max(S.Integer(1), 3*C)**g * (3*C)
            assert actual <= major
            count_budget += 1
print(f'PASS exact_derivatives={count_exact} triangle_bounds={count_triangle} local_finite_envelopes={count_budget}')
