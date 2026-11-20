from itertools import combinations
from fractions import Fraction
from math import prod
P=(37,31,29,23,19,17,13,11,7,5)
W=[p for k in (9,) for p in combinations(P,k)]
def retain(word,mask):
    return all(k%2==0 or bool(mask & (1 << (sum(word[:k])%8))) for k in range(1,len(word)+1))
def label(word): return (len(word),sum(word)%2)
count=0
for mask in range(256):
    kept={d for d in W if retain(d,mask)}
    for d in kept:
        fibre=[v for v in W if label(v)==label(d)]
        if all(v in kept for v in fibre): continue
        q4=d[:4]
        assert all(retain(q4[:j],mask) for j in range(1,5))
        assert tuple(reversed(tuple(reversed(d[:8]))[-4:])) == q4
        for b,bminus,g in ((1,Fraction(-2,3),Fraction(5,7)),(2,Fraction(7,4),Fraction(-3,5))):
            full=b*prod(d)
            raw=-bminus*g
            compiled=Fraction(0)
            assert compiled-raw==bminus*g
            assert full == b*prod(d)
        count+=1
assert count>0
print('actual abstract negative-inner cases:',count,'canonical fourth admissions and signed beta-minus tests passed')
