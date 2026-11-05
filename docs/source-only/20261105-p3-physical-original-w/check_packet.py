"""Finite algebraic regression only; it does not validate Lean proofs."""
from math import exp, log, gcd, prod
from random import Random
rng = Random(1729)
checks = 0
for _ in range(750):
    d, g = rng.randrange(1, 8), rng.randrange(1, 6)
    group = [rng.randrange(g) for _ in range(d)]
    U = [rng.randrange(1, 6) for _ in range(d)]
    n = [rng.randrange(1, 7) for _ in range(d)]
    z = [log(n[i] / U[i]) for i in range(d)]
    bases, orig, group_logs = [1.0]*g, [1.0]*g, [0.0]*g
    for i,j in enumerate(group):
        bases[j] *= U[i]
        orig[j] *= n[i]
        group_logs[j] += z[i]
        assert abs(U[i]*exp(z[i])-n[i]) < 1e-9
    for j in range(g):
        assert abs(bases[j]*exp(group_logs[j])-orig[j]) < 1e-8
        assert abs(log(orig[j])-(log(bases[j])+group_logs[j])) < 1e-9
    complete = prod(n)
    assert complete == round(prod(orig))
    W = lambda p: sum((-1)**j*v/(j+1) for j,v in enumerate(p)) + p[0]*p[-1]/100
    assert abs(W(orig)-W([bases[j]*exp(group_logs[j]) for j in range(g)])) < 1e-7
    q,T = rng.randrange(1,21),rng.randrange(1,181)
    phi = sum(gcd(i,q)==1 for i in range(q))
    k = lambda p: (1.0 if p%q==T%q else 0.0)-(1.0/phi if gcd(p,q)==1 else 0.0)
    assert k(complete)==k(round(prod(orig)))
    checks+=1
print(f"PASS {checks} positive slots/original groups/complete modulus/coprime means")
