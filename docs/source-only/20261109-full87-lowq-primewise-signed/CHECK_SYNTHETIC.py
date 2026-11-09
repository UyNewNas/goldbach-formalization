from fractions import Fraction as F
from random import Random
from math import gcd
r = Random(20261109)
P = [p for p in range(2, 110)
     if all(p % d for d in range(2, int(p**0.5)+1))]
strict = 0
for k in range(1200):
    N = 2 * r.randint(55, 120)
    T = [p for p in P if p <= N+10]
    Ds = list(range(1, 13))
    A = {d: F(r.randint(-4, 4), r.randint(1, 5)) for d in Ds}
    W = {p: F(r.randint(-5, 5), r.randint(1, 7)) for p in T}
    X = r.randint(0, 12)
    Q = [d for d in Ds if d <= X]
    H = [d for d in Ds if d > X]
    def phi(d): return sum(gcd(a, d) == 1 for a in range(d))
    def contrast(p, d):
        return F((p-N) % d == 0) - F(gcd(p, d) == 1, phi(d))
    def prim(d):
        return sum((W[p]*contrast(p, d) for p in T), F(0))
    low = sum((A[d]*prim(d) for d in Q), F(0))
    high = sum((A[d]*prim(d) for d in H), F(0))
    full = sum((A[d]*prim(d) for d in Ds), F(0))
    kernel = {p: sum((A[d]*contrast(p, d) for d in Q), F(0))
              for p in T}
    per_prime = sum((W[p]*kernel[p] for p in T), F(0))
    envelope = sum((abs(W[p])*abs(kernel[p]) for p in T), F(0))
    per_q = sum((abs(A[d])*sum(
         (abs(W[p])*abs(contrast(p, d)) for p in T), F(0))
         for d in Q), F(0))
    assert low == per_prime
    assert abs(low) <= envelope
    assert abs(high) <= abs(full) + envelope
    assert envelope <= per_q
    strict += envelope < per_q
print('exact Fraction models: 1200 PASS, strict synthetic improvements:', strict)
# Synthetic algebra only; NOT saved87 data nor Lean/kernel acceptance.
