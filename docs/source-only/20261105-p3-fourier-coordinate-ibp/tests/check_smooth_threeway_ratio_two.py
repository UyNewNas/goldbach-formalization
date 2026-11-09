"""Finite sanity check for smooth three-child HB dyadic refinement.
Not a Lean proof or a proof of C-infinity of the cutoff.
"""
from math import exp

def bump(x):
    return 0.0 if x <= 0 else exp(-1.0/x)

def chi(t):
    if t <= 1: return 1.0
    if t >= 2: return 0.0
    a, b = bump(t-1), bump(2-t)
    return b/(a+b)

def psi(t):
    return chi(t)-chi(2*t)

def gates(t):
    return (chi(4*t-2), chi(4*t-3)-chi(4*t-2), 1-chi(4*t-3))

def lower(L):
    return (L/2, 3*L/4, L)

case=live=overlap=seam=0
max_dev=0.
for j in range(7):
    L=2**j
    for k in range(401):
        t=k/100
        g=gates(t)
        max_dev=max(max_dev,abs(sum(g)-1),
            abs(sum(psi(t)*v for v in g)-psi(t)))
        assert all(-1e-12<=v<=1+1e-12 for v in g)
        for a,value in enumerate(g):
            if abs(psi(t)*value)>1e-12:
                x=L*t
                lo=lower(L)[a]
                assert lo<x<2*lo,(j,t,a,x,lo)
                live+=1
        overlap+=sum(v>1e-12 for v in g)>1
        seam+=t==1
        case+=1
assert max_dev<1e-12
print(dict(cutoff_cases=case,live_child_cases=live,overlap_cases=overlap,
    base_seams=seam,max_partition_error=max_dev,failures=0))
