#!/usr/bin/env python3
"""Independent finite probes of P3HBSmoothLogScaleBudget; not Lean/kernel proof."""
from fractions import Fraction
from itertools import product
import math

def chi_exact(t):
    if t <= 1: return Fraction(1)
    if t >= 2: return Fraction(0)
    return 2-t

def gate(chi,t,a):
    return [chi(4*t-2),chi(4*t-3)-chi(4*t-2),1-chi(4*t-3)][a]

def coord(chi,x,j,a):
    L=Fraction(2)**j
    t=x/L
    return (chi(t)-chi(2*t))*gate(chi,t,a)

exact=0
child_active=0
for j in range(11):
    L=Fraction(2)**j
    for num in range(1,49):
        t=Fraction(num,24)
        x=L*t
        original=chi_exact(t)-chi_exact(2*t)
        values=[coord(chi_exact,x,j,a) for a in range(3)]
        assert sum(values)==original
        for a in range(3):
            assert values[a]==original*gate(chi_exact,t,a)
            assert abs(gate(chi_exact,t,a)) <= 2
            assert abs(values[a]) <= 2*abs(original)
            if values[a]: child_active+=1
            exact+=1

for p in range(128):
    labels=[(p+i)%7 for i in range(6)]
    ts=[Fraction((p+3*i)%37+12,24) for i in range(6)]
    parents=[chi_exact(t)-chi_exact(2*t) for t in ts]
    parent=math.prod(parents)
    for a in product(range(3),repeat=6):
        child=math.prod(parents[i]*gate(chi_exact,ts[i],a[i]) for i in range(6))
        assert abs(child) <= 64*abs(parent)

def bump(t):
    if t<=0: return 0.0
    return math.exp(-1.0/t)
def chi_smooth(t):
    if t<=1: return 1.0
    if t>=2: return 0.0
    a=bump(2-t)
    b=bump(t-1)
    return a/(a+b)
def logtemplate(u,a):
    t=math.exp(u)
    return (chi_smooth(t)-chi_smooth(2*t))*gate(chi_smooth,t,a)
def fd(f,u,step=2e-5):
    return (f(u+step)-f(u-step))/(2*step)
errors=[]
for j in (0,1,3,8,17,37):
    L=2.0**j
    for u in (-1.7,-1.1,-math.log(2),-.45,-.2,0,.15,.38,math.log(2),1,1.4):
        for a in range(3):
            f=lambda z:coord(chi_smooth,L*math.exp(z),j,a)
            assert abs(f(u)-logtemplate(u,a)) < 3e-14
            errors.append(abs(fd(f,u)-fd(lambda z:logtemplate(z,a),u)))
assert max(errors)<1e-9,max(errors)
print(f'PASS exact coordinate tests={exact}, nonzero children={child_active}, 6-slot tests={128*729}, log-derivative tests={len(errors)}, maximum numeric derivative difference={max(errors):.3g}')
