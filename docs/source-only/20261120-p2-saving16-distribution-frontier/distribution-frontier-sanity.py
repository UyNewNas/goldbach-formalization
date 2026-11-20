from itertools import combinations
from fractions import Fraction as F
from math import prod,gcd
P=(13,11,7,5,3)
S=(6,10,14,15,21,22,26,33,35,39,55,65,77)
N=130
words=[p for k in range(6) for p in combinations(P,k)]
def phi(n): return sum(gcd(n,j)==1 for j in range(1,n+1))
def discrepancy(m):
    return F(sum((x-N)%m==0 for x in S))-F(sum(gcd(x,m)==1 for x in S),phi(m))
def label(d): return (len(d),sum(d)%2)
for mask in range(128):
    def retain(d): return all(k%2==0 or bool(mask & (1<<(sum(d[:k])%7))) for k in range(1,len(d)+1))
    raw=compiled=plus=minus=F(0)
    for d in words:
        dmod=prod(d); pos=len(d)%2==0; keep=retain(d)
        fibre=[v for v in words if label(v)==label(d)]
        outer=any(retain(v) for v in fibre); inner=all(retain(v) for v in fibre)
        for sm,bplus,bminus in ((1,F(2,3),F(-1,2)),(2,F(-3,5),F(4,7))):
            G=discrepancy(sm*dmod)
            selected=bplus if pos else bminus
            if keep: raw+=(1 if pos else -1)*selected*G
            if (outer if pos else inner): compiled+=(1 if pos else -1)*selected*G
            if pos and outer and not keep: plus+=selected*G
            if not pos and keep and not inner: minus+=selected*G
    assert compiled==raw+plus+minus
print('128 synthetic policies: same full-q signed discrepancy equals raw plus both compiler families')
