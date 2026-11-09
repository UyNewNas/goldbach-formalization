#!/usr/bin/env python3
"""Exact Fraction synthetic regression; NOT original saved87 witness replay."""
from fractions import Fraction
from random import Random
from math import gcd

rng = Random(20261120)
primes = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37]

def phi(n):
    return sum(gcd(k, n) == 1 for k in range(1, n + 1))

def kappa(N, p, d):
    return Fraction(int((p-N)%d == 0)) - (
        Fraction(1, phi(d)) if gcd(p,d) == 1 else Fraction(0))

negative_W = negative_cross = strict_cs = d1_cases = 0
for trial in range(1800):
    N = rng.randrange(6, 200, 2)
    X = rng.randrange(1, 50)
    Q = [d for d in range(1, 36) if d <= X and rng.randrange(3)]
    T = rng.sample(primes, rng.randint(0, len(primes)))
    A = {d: Fraction(rng.randrange(-5,6), rng.randrange(1,7)) for d in Q}
    W = {p: Fraction(rng.randrange(-7,8), rng.randrange(1,9)) for p in T}
    negative_W += int(any(W[p] < 0 for p in T))
    d1_cases += int(1 in Q)
    K = {(p,d): kappa(N,p,d) for p in T for d in Q}
    h = {p: sum((A[d]*K[(p,d)] for d in Q), Fraction()) for p in T}
    primitive = {d: sum((W[p]*K[(p,d)] for p in T), Fraction()) for d in Q}
    low = sum((A[d]*primitive[d] for d in Q), Fraction())
    primewise = sum((W[p]*h[p] for p in T), Fraction())
    gram = sum((abs(W[p])*h[p]**2 for p in T), Fraction())
    pair_gram = sum((A[d]*A[e]*sum((abs(W[p])*K[(p,d)]*K[(p,e)]
                                for p in T), Fraction())
                     for d in Q for e in Q), Fraction())
    mass = sum((abs(W[p]) for p in T), Fraction())
    l1 = sum((abs(W[p])*abs(h[p]) for p in T), Fraction())
    assert low == primewise and gram == pair_gram
    assert low*low <= l1*l1 <= mass*gram, (trial,low,mass,gram)
    assert gram >= 0
    assert all(K[(p,1)] == 0 for p in T if 1 in Q)
    strict_cs += int(low*low < mass*gram)
    diagonal = sum((A[d]**2 * sum((abs(W[p])*K[(p,d)]**2 for p in T),Fraction())
                    for d in Q),Fraction())
    negative_cross += int(gram-diagonal < 0)
print(f"exact_fraction_trials=1800 mismatches=0 negative_weight_cases={negative_W} "
      f"negative_cross_cases={negative_cross} strict_weighted_cs={strict_cs} q1_cases={d1_cases}")
