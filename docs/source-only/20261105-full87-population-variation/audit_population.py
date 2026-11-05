#!/usr/bin/env python3
"""Synthetic exact finite checks only; not original87 archive or Lean."""
from fractions import Fraction as Q
from math import gcd
from random import Random
rng = Random(20261107)
checks = 0
def primes(n):
    return [p for p in range(2, n+1)
            if all(p%q for q in range(2, int(p**.5)+1))]
def phi(n):
    return sum(gcd(k,n)==1 for k in range(1,n+1))
for N in range(95):
    ps=primes(N)
    divN=sum(N%p==0 for p in ps)
    for d in range(65):
        ph=phi(d)
        mod=Q(sum(d%p==0 for p in ps),ph) if ph else Q(0)
        den=Q(1,ph) if ph else Q(0)
        cen=sum(N%p==0 and ((p-N)%d==0 if d else p==N) for p in ps)
        assert cen<=divN and mod<=len(ps)*den
        checks+=2
def prod(xs):
    v=1
    for x in xs: v*=x
    return v
def leaves(level,rem,pre=(),sgn=1):
    if not rem: return [(pre,sgn)]
    p,*rest=rem
    out=leaves(level,rest,pre,sgn)
    if (level+3*len(pre)+p+sum(pre))%5<=2:
        out+=leaves(level,rest,(p,)+pre,-sgn)
    return out
def signed(level,rem,G,beta):
    return sum(sgn*sum((beta[0] if sgn>0 else beta[1])*
             G[(a*prod(word))%len(G)] for a in (2,3,5))
             for word,sgn in leaves(level,rem))
def envelope(level,rem,H,beta):
    return sum(sum(abs(beta[0] if sgn>0 else beta[1])*
             H[(a*prod(word))%len(H)] for a in (2,3,5))
             for word,sgn in leaves(level,rem))
for _ in range(2500):
    rem=[rng.choice([2,3,5,7,11]) for _ in range(rng.randrange(7))]
    a,b=rng.randint(1,11),rng.randint(1,11)
    beta=Q(rng.randint(-6,5),7),Q(rng.randint(-4,5),9)
    G=[Q(rng.randint(-9,9),7) for _ in range(12)]
    H=[abs(v)+Q(rng.randint(0,4),10) for v in G]
    value=signed(a,rem,G,beta)-signed(b,rem,G,beta)
    assert abs(value)<=envelope(a,rem,H,beta)+envelope(b,rem,H,beta)
    checks+=1
assert checks==14850
print("PASS",checks,"synthetic exact cases; not Lean or original87 replay")
