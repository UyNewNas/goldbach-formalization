#!/usr/bin/env python3
"""Exact finite polynomial check of canonical D_j D_i(W*G); NOT a Lean/kernel proof."""
import sympy as s
from itertools import product
x = s.symbols("x0:6")
W = 2*x[0]**2*x[1]+3*x[1]*x[2]**2+x[3]*x[4]*x[5]+x[0]*x[2]*x[5]+7*x[4]**2-x[2]*x[3]
orders=(0,1,1,0,1,0)
points=[{z:s.Rational(i+2,3) for i,z in enumerate(x)},
        {z:s.Rational(2*i-5,4) for i,z in enumerate(x)}]
checked=0
for a in [(0,1,2,0,1,2),(2,2,0,1,0,1)]:
    F=[(x[t]+s.Integer(1+a[t]))**(1+orders[t]) for t in range(6)]
    G=s.prod(F)
    weighted=W*G
    for i,j in product(range(6),repeat=2):
        d1=s.diff(weighted,x[i])
        formal1=s.diff(W,x[i])*G+W*s.diff(G,x[i])
        d2=s.diff(weighted,x[i],x[j])
        formal2=(s.diff(W,x[j],x[i])*G+
          s.diff(W,x[i])*s.diff(G,x[j])+
          s.diff(W,x[j])*s.diff(G,x[i])+
          W*s.diff(G,x[i],x[j]))
        for p in points:
            assert d1.subs(p)==formal1.subs(p)
            assert d2.subs(p)==formal2.subs(p)
            checked+=2
print(f"PASS {checked}/{checked} exact rational evaluations (i=j and i!=j)")
