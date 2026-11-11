"""Finite exact algebra regression; polynomial chi is NOT a C∞ plateau cutoff.
Only finite derivative-level partition identities are tested; not Lean or PP.
"""
from itertools import product
import sympy as s
x=s.Symbol("x")
chi=lambda z: 1-z/3+z**2/7
psi=s.expand(chi(x)-chi(2*x))
g=[s.expand(chi(4*x-2)),s.expand(chi(4*x-3)-chi(4*x-2)),s.expand(1-chi(4*x-3))]
ch=[s.expand(psi*v) for v in g]
def D(f,k):
    for _ in range(k): f=s.expand(x*s.diff(f,x))
    return s.expand(f)
xs=[s.Rational(t) for t in ("1/2","3/4","1","5/4","3/2","7/4")]
n=0
assert s.expand(sum(g)-1)==0;n+=1
assert s.expand(sum(ch)-psi)==0;n+=1
for k in range(5):
    assert s.expand(sum(D(f,k) for f in ch)-D(psi,k))==0;n+=1
    for t in xs:
        assert s.cancel(sum(D(f,k).subs(x,t) for f in ch)-D(psi,k).subs(x,t))==0;n+=1
for orders in [(0,0,0,0,0,0),(0,1,2,3,0,1),(4,3,2,1,0,4),
               (1,1,1,1,1,1),(2,0,3,1,4,2)]:
    A=[[D(ch[a],orders[i]).subs(x,xs[i]) for a in range(3)] for i in range(6)]
    actual=sum(s.prod(A[i][a[i]] for i in range(6)) for a in product(range(3),repeat=6))
    expected=s.prod(D(psi,orders[i]).subs(x,xs[i]) for i in range(6))
    assert s.factor(actual-expected)==0;n+=1
for j in (0,1,3,17):
    for t in xs:
        phys=s.Integer(2)**j*t
        for a in range(3):
            scaled=(chi(phys/s.Integer(2)**j)-chi(2*phys/s.Integer(2)**j))*g[a].subs(x,phys/s.Integer(2)**j)
            assert s.factor(scaled-ch[a].subs(x,t))==0;n+=1
print(f"PASS {n}/{n} exact rational/symbolic cases; 729 children per six-slot test")
