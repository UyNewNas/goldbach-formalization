"""Finite exact surrogate for P3.6 separated HB L1 bound.

NOT a Lean/Lake/kernel test and NOT a proof of continuous Lebesgue integration.
Two unit cells approximate the compact interval [-1,1]. The analytic
argument needs the *actual* interval [-log 2,log 2] and pinned mathlib.
"""
from fractions import Fraction as Q
from itertools import product
from math import comb, factorial

# F_a(u) = w_a (1-u^2)^4 on [-1,1], zero outside; C^3 at seams.
# The sum over the actual three labelled children is the base polynomial.
weights = (Q(1, 6), Q(1, 3), Q(1, 2))
assert sum(weights) == 1
points = (Q(-1, 2), Q(1, 2))


def deriv(k, a, u):
    if abs(u) > 1:
        return Q(0)
    ans = Q(0)
    for j in range(5):
        p = 2*j
        if p >= k:
            ans += Q((-1)**j*comb(4, j)*factorial(p), factorial(p-k)) * u**(p-k)
    return weights[a]*ans


# Uniform, rigorously valid for |u|<=1 by coefficient triangle inequality.
def bound(k):
    return sum(Q(comb(4, j)*factorial(2*j), factorial(2*j-k))
               for j in range(5) if 2*j >= k)


C = max(bound(k) for k in range(3))
assert C == 256
checks = 0
for orders in [(0,)*6, (1,0,2,1,0,2), (2,)*6]:
    axis = {(a,k):sum(abs(deriv(k,a,u)) for u in points)
            for a in range(3) for k in set(orders)}
    for (a,k),mass in axis.items():
        assert mass <= 2*C
        checks += 1
    exact_tensor_mass = Q(0)
    for child in product(range(3), repeat=6):
        separated = Q(1)
        for i in range(6):
            separated *= axis[child[i],orders[i]]
        # Exact finite product/sum Fubini on two unit-measure cells.
        cube = sum((__import__('math').prod(
                   abs(deriv(orders[i],child[i],point[i])) for i in range(6)))
                   for point in product(points,repeat=6))
        assert cube == separated
        assert separated <= (2*C)**6
        exact_tensor_mass += separated
        checks += 1
    assert exact_tensor_mass <= 729*(2*C)**6
    checks += 1
print(f'PASS cases={checks} C={C} child_count=729 model=2-cell-counting-measure')
