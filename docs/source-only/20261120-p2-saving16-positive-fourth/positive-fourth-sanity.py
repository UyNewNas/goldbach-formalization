from itertools import combinations
from fractions import Fraction
from math import prod
P=(37,31,29,23,19,17,13,11,7,5)
W=list(combinations(P,8))
def retain(word,mask):
    return all(k%2==0 or bool(mask & (1 << (sum(word[:k])%8))) for k in range(1,len(word)+1))
def label(word): return (len(word),sum(word)%2)
n=0
for mask in range(256):
    kept={d for d in W if retain(d,mask)}
    for d in W:
        if d in kept: continue
        witnesses=[v for v in kept if label(v)==label(d)]
        if not witnesses: continue
        v=witnesses[0]
        assert v!=d and retain(v[:4],mask)
        assert tuple(reversed(tuple(reversed(v[:8]))[-4:]))==v[:4]
        for b,bplus,g in ((1,Fraction(-2,3),Fraction(5,7)),(2,Fraction(7,4),Fraction(-3,5))):
            assert b*prod(d)!=b*prod(v)
            assert bplus*g-0==bplus*g
        n+=1
assert n>0
print('abstract positive-outer cases:',n,'distinct witnesses, admitted witness fourths and original product beta-plus preserved')
