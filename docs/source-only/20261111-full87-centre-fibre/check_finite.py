#!/usr/bin/env python3
"""Finite synthetic verification only; NOT original87 source replay or Lean elaboration."""
from fractions import Fraction
from random import Random

def prime(p):
    return p >= 2 and all(p % k for k in range(2, int(p ** .5) + 1))

def centre(N, d):
    return sum(1 for p in range(N + 1) if prime(p) and N % p == 0 and (p-N) % d == 0) if d else sum(1 for p in range(N + 1) if prime(p) and N % p == 0 and p == N)

def fibre(N, d):
    return sum(1 for p in range(N + 1) if prime(p) and N % p == 0 and ((p-N) % d == 0 if d else p == N))

rng = Random(20261111)
checks = 0
for N in range(0, 102):
    for d in range(0, 103):
        assert centre(N,d) == fibre(N,d)
        checks += 1
        if N > 2 and N % 2 == 0:
            for p in range(N + 1):
                if prime(p) and N % p == 0 and ((p-N) % d == 0 if d else p == N):
                    assert p < N and d != 0 and (N-p) % d == 0

signed_cases = 0
for _ in range(5000):
    N = rng.randrange(0, 105)
    # Distinct full moduli but with independent old/new coefficients and overlap.
    A = set(rng.sample(range(0, 70), rng.randrange(0, 16)))
    B = set(rng.sample(range(0, 70), rng.randrange(0, 16)))
    old = {d: Fraction(rng.randrange(-8,9),rng.randrange(1,9)) for d in A}
    new = {d: Fraction(rng.randrange(-8,9),rng.randrange(1,9)) for d in B}
    rho = {d:old.get(d,0)-new.get(d,0) for d in (A|B)}
    left = sum((v*centre(N,d) for d,v in rho.items()), Fraction(0))
    cps = [p for p in range(N + 1) if prime(p) and N % p == 0]
    right = sum((sum((v for d,v in rho.items() if d and (p-N) % d == 0),Fraction(0)) +
                 sum((v for d,v in rho.items() if d == 0 and p==N),Fraction(0)) for p in cps),Fraction(0))
    invoice = sum((sum((abs(v) for d,v in rho.items() if d and (p-N) % d == 0),Fraction(0)) +
                   sum((abs(v) for d,v in rho.items() if d == 0 and p==N),Fraction(0)) for p in cps),Fraction(0))
    assert left == right and abs(left) <= invoice, (N,old,new,left,right,invoice)
    signed_cases += 1
print(f'centre AP counts: {checks}; signed full-modulus synthetic cases: {signed_cases}; failures: 0')
