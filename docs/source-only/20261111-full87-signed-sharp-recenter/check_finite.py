#!/usr/bin/env python3
"""Exact finite-algebra audit only. NOT Lean elaboration, PP or original87 replay."""
from fractions import Fraction
from math import gcd
from random import Random

def primes_up_to(n):
    return [p for p in range(2, n + 1) if all(p % j for j in range(2, int(p ** .5) + 1))]

def phi(n):
    return sum(gcd(j, n) == 1 for j in range(1, n + 1))

def prime_data(N, d):
    ps = primes_up_to(N)
    tot = phi(d)
    ap = sum((p - N) % d == 0 for p in ps)
    coprime = sum(gcd(p, d) == 1 for p in ps)
    modulus = sum(d % p == 0 for p in ps)
    centre = sum(N % p == 0 and (p - N) % d == 0 for p in ps)
    exact = Fraction(coprime, tot)
    density = Fraction(1, tot)
    sharp = Fraction(ap) - len(ps) * density
    primitive = Fraction(ap) - exact
    receiver = Fraction(ap - centre)
    assert primitive == sharp + Fraction(modulus, tot)
    assert receiver == len(ps) * density + sharp - centre
    return density, sharp, primitive, Fraction(modulus, tot), Fraction(centre), receiver

records = {}
count = 0
for N in range(4, 102, 2):
    for d in range(1, 91):
        records[(N, d)] = prime_data(N, d)
        count += 1

rng = Random(0x87A14)
signed_tests = 0
for i in range(5000):
    N = rng.randrange(2, 51) * 2
    pool = list(range(1, 91))
    old = {x for x in pool if rng.randrange(7) == 0}
    new = {x for x in pool if rng.randrange(7) == 0}
    a = {d: Fraction(rng.randrange(-7, 8), rng.randrange(1, 8)) for d in old}
    b = {d: Fraction(rng.randrange(-7, 8), rng.randrange(1, 8)) for d in new}
    union = old | new
    rho = {d: a.get(d, 0) - b.get(d, 0) for d in union}
    for idx in (1, 2, 4, 5):
        old_sum = sum((a[d] * records[(N, d)][idx] for d in old), Fraction())
        new_sum = sum((b[d] * records[(N, d)][idx] for d in new), Fraction())
        merged = sum((rho[d] * records[(N, d)][idx] for d in union), Fraction())
        assert old_sum - new_sum == merged
        signed_tests += 1
    receiver_gain = sum((rho[d] * records[(N, d)][5] for d in union), Fraction())
    density_gain = sum((rho[d] * records[(N, d)][0] for d in union), Fraction())
    sharp_gain = sum((rho[d] * records[(N, d)][1] for d in union), Fraction())
    centre_gain = sum((rho[d] * records[(N, d)][4] for d in union), Fraction())
    assert receiver_gain - len(primes_up_to(N)) * density_gain == sharp_gain - centre_gain

# A signed PP estimate cannot control the absolute leaf invoice.
assert abs(Fraction(1) - Fraction(1)) == 0
assert abs(Fraction(1)) + abs(Fraction(-1)) == 2
print(f"PASS: {count} exact prime-mean recenterings, {signed_tests} signed modulus-union identities,")
print("      5000 receiver cancellations, explicit signed-vs-absolute counterexample.")
