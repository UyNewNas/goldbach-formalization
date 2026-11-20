from itertools import combinations
from fractions import Fraction
from math import prod

primes = (7,5,3,2)
words = [tuple(c) for k in range(5) for c in combinations(primes,k)]
small = ((1, Fraction(1), Fraction(1)), (11, Fraction(2,3), Fraction(-1,2)))
def g(m): return Fraction((m % 11)-5, 3)
def label(word): return (len(word), sum(word) % 2)
def test(positive, word):
    return sum((bp if positive else bm) * g(b * prod(word)) for b,bp,bm in small)
def run(mask):
    def allow(word): return len(word)%2 == 0 or bool(mask & (1 << (sum(word) % 8)))
    def walk(prefix, left, positive, mode):
        if mode == 'front' and len(prefix)==4: return test(positive,prefix) * (1 if positive else -1)
        if not left:
            if mode=='stop' and len(prefix)>=4: return 0
            if mode=='front': return 0
            return test(positive,prefix) * (1 if positive else -1)
        p,*tail=left
        value=walk(prefix,tail,positive,mode)
        nxt=prefix+(p,)
        if allow(nxt): value+=walk(nxt,tail,not positive,mode)
        return value
    retained=[]
    def leaves(prefix,left):
        if not left:
            retained.append(prefix); return
        p,*tail=left
        leaves(prefix,tail)
        nxt=prefix+(p,)
        if allow(nxt): leaves(nxt,tail)
    leaves((),list(primes))
    kept=set(retained)
    raw=sum((1 if len(d)%2==0 else -1)*test(len(d)%2==0,d) for d in kept)
    assert raw==walk((),list(primes),True,'all')
    assert raw==walk((),list(primes),True,'stop')+walk((),list(primes),True,'front')
    compiled=Fraction(0); pos=Fraction(0); neg=Fraction(0)
    for d in words:
        fibre=[v for v in words if label(v)==label(d)]
        outer=any(v in kept for v in fibre); inner=all(v in kept for v in fibre)
        positive=len(d)%2==0
        admitted=outer if positive else inner
        value=test(positive,d)
        if admitted: compiled+=(1 if positive else -1)*value
        if positive and outer and d not in kept: pos+=value
        if not positive and d in kept and not inner: neg+=value
    assert compiled==raw+pos+neg
for k in range(256): run(k)
print('256 abstract policies: full signed tree, rank-four split and both weighted corrections agree')
