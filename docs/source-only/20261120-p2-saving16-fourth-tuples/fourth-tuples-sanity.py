from fractions import Fraction
from math import prod
P = (17, 13, 11, 7, 5, 3)
small = ((1, Fraction(2,3), Fraction(3,4)), (2, Fraction(-1,7), Fraction(5,6)))
def G(n): return Fraction((n % 19) - 8, 13)
def terminal(chosen):
    positive = len(chosen) % 2 == 0
    return (1 if positive else -1) * sum((bp if positive else bm)*G(b*prod(chosen)) for b,bm,bp in small)
def check(mask):
    def allowed(word): return len(word)%2 == 0 or bool(mask & (1 << (sum(word)%7)))
    def tree(prefix,remaining):
        if not remaining: return terminal(prefix)
        p,*tail=remaining
        out=tree(prefix,tail)
        if allowed(prefix+(p,)): out+=tree(prefix+(p,),tail)
        return out
    states=[]
    def collect(prefix,remaining):
        if len(prefix)==4:
            states.append((prefix,tuple(remaining))); return 0
        if not remaining: return terminal(prefix)
        p,*tail=remaining
        out=collect(prefix,tail)
        if allowed(prefix+(p,)): out+=collect(prefix+(p,),tail)
        return out
    stopped=collect((),list(P))
    assert len(states)==len({x for x,_ in states})
    for prefix,remaining in states:
        assert all(prefix[i]>prefix[i+1] for i in range(3))
        assert remaining==tuple(x for x in P if x<prefix[-1])
    assert tree((),list(P))==stopped+sum(tree(p,list(rest)) for p,rest in states)
for mask in range(128): check(mask)
print('128 abstract policies: ordered quadruples are unique; original remainder and signed full-q continuation are preserved')
