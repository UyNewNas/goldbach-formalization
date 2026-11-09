#!/usr/bin/env python3
"""Toy exact rational tests only, NOT Lean elaboration or saved87 replay."""
from fractions import Fraction
from random import Random
from math import gcd

rng = Random(20261109)
primes = [2,3,5,7,11,13,17,19,23,29,31,37]

def phi(n):
    return sum(gcd(k,n)==1 for k in range(1,n+1))

def contrast(N,p,d):
    return Fraction(int((p-N)%d==0)) - (Fraction(1,phi(d)) if gcd(p,d)==1 else Fraction())

strict_cross=0
negative_cross=0
for trial in range(1500):
    N=rng.randrange(6,200,2)
    X=rng.randrange(1,60)
    Q=[d for d in range(1,35) if d<=X and rng.randrange(3)]
    T=rng.sample(primes,rng.randint(0,len(primes)))
    A={d:Fraction(rng.randrange(-5,6),rng.randrange(1,7)) for d in Q}
    k={(p,d):contrast(N,p,d) for p in T for d in Q}
    kernel=lambda p:sum((A[d]*k[(p,d)] for d in Q),Fraction())
    left=sum((kernel(p)**2 for p in T),Fraction())
    right=sum((A[d]*A[e]*sum((k[(p,d)]*k[(p,e)] for p in T),Fraction()) for d in Q for e in Q),Fraction())
    assert left == right and right>=0, (trial,left,right)
    off=sum((A[d]*A[e]*sum((k[(p,d)]*k[(p,e)] for p in T),Fraction()) for d in Q for e in Q if d!=e),Fraction())
    diag=sum((A[d]*A[d]*sum((k[(p,d)]**2 for p in T),Fraction()) for d in Q),Fraction())
    assert left==diag+off
    strict_cross+=int(off!=0)
    negative_cross+=int(off<0)
    assert all(k[(p,1)]==0 for p in T if 1 in Q)
print(f"exact_fraction_trials={trial+1} mismatches=0 nonzero_offdiagonal={strict_cross} negative_offdiagonal={negative_cross}")
