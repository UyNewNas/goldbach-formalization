#!/usr/bin/env python3
"""Exact synthetic arithmetic regression for changed rank-eight source.

No Lean/kernel, no archive evaluation and no claim about any asymptotic estimate.
"""
from fractions import Fraction as Q
from random import Random
from math import gcd
from pathlib import Path
import hashlib
import json

RNG = Random(20261105)
CASES = 0

def verify(pred, msg):
    global CASES
    assert pred, msg
    CASES += 1

def primes_upto(n):
    return [k for k in range(2, n + 1) if all(k % j for j in range(2, int(k ** .5) + 1))]

def phi(n):
    if n == 0: return 0
    return sum(gcd(k, n) == 1 for k in range(1, n + 1))

def receiver(N, d, ps):
    # Actual receiver labels N-p; omit centre-divisors first.
    return Q(sum((N - p) % d == 0 if d else N == p for p in ps if N % p), 1)

def raw_ap(N, d, ps):
    return Q(sum((p - N) % d == 0 if d else p == N for p in ps), 1)

def centre(N, d, ps):
    return Q(sum(((p - N) % d == 0 if d else p == N) and N % p == 0 for p in ps), 1)

def density(d):
    return Q(1, phi(d)) if phi(d) else Q(0)

def mod_prime(N, d, ps):
    return Q(sum(d % p == 0 for p in ps), phi(d)) if phi(d) else Q(0)

def mean(N, d, ps):
    return Q(sum(gcd(p, d) == 1 for p in ps), phi(d)) if phi(d) else Q(0)

# First verify same-full-modulus finite algebra, with d=0 and d=1 boundaries.
for N in range(0, 61):
    ps = primes_upto(N)
    for d in range(0, 35):
        e = raw_ap(N, d, ps) - mean(N, d, ps)
        residual = e - mod_prime(N, d, ps) - centre(N, d, ps)
        verify(receiver(N, d, ps) == raw_ap(N, d, ps) - centre(N, d, ps), 'receiver')
        verify(mean(N, d, ps) == len(ps) * density(d) - mod_prime(N, d, ps), 'mean')
        verify(receiver(N, d, ps) == len(ps) * density(d) + residual, 'residual')

# Local signed continuations. Incoming occurrences may repeat and have independent signs.
# A "level" only affects the test through continuation weights, not the list owner.
def continuation(level, state, test):
    # Distinct positive / negative beta factors, with exactly the same full moduli.
    total = Q(0)
    for d, sgn, base in state['leaves']:
        beta = Q(3, 2) if sgn else Q(5, 3)
        total += base * beta * (Q(1) if ((d + level) % 3 != 0) else Q(0)) * test(d)
    return total

def saving(state, test):
    return continuation(state['old'], state, test) - continuation(state['new'], state, test)

for rep in range(500):
    N = RNG.randrange(2, 61)
    ps = primes_upto(N)
    states = []
    for i in range(RNG.randrange(0, 11)):
        old = RNG.randrange(1, 8)
        new = old if RNG.randrange(3) else RNG.randrange(1, 8)
        dvals = [RNG.randrange(1, 25) for _ in range(RNG.randrange(0, 4))]
        states.append({'owner': RNG.choice([None, 0, 1, 2, 3]), 'old':old,
                       'new':new, 'leaves':[(d, RNG.randrange(2), Q(RNG.randrange(-4,5))) for d in dvals]})
    # Deliberately duplicate an occurrence (not a set).
    if states and RNG.randrange(2): states.append(states[0])
    test_values = {d:Q(RNG.randrange(-4,5)) * Q(d + 1) for d in range(1,30)}
    test = lambda d: test_values[d]
    physical_gain = sum((saving(s, test) for s in states if s['owner'] is not None), Q(0))
    changed = [s for s in states if s['owner'] is not None and s['old'] != s['new']]
    changed_gain = sum((saving(s, test) for s in changed), Q(0))
    verify(physical_gain == changed_gain, 'changed owner/list partition')
    verify(abs(changed_gain) <= sum((abs(saving(s, test)) for s in changed), Q(0)), 'local abs')
    residual = lambda d: raw_ap(N,d,ps)-mean(N,d,ps)-mod_prime(N,d,ps)-centre(N,d,ps)
    # the arithmeticResidual definition already includes the modality correction once
    # so the actual identity is AP-mean - modulus - centre.
    recv = lambda d: receiver(N,d,ps)
    gain = lambda f: sum((saving(s, f) for s in states if s['owner'] is not None), Q(0))
    verify(gain(recv) == Q(len(ps))*gain(density)+gain(residual), 'receiver gain')
    verify(abs(gain(recv)-Q(len(ps))*gain(density)) <=
           sum((abs(saving(s,residual)) for s in changed), Q(0)), 'signed residual budget')

# A dense unchanged predecessor may contribute a large old+new absolute budget,
# but contributes exactly zero to the new changed-only ledger.
s = {'owner':0,'old':4,'new':4,'leaves':[(5,True,Q(1000)),(7,False,Q(-2000))]}
verify(saving(s,lambda d: Q(1)) == 0, 'identical level no cost')

root=Path(__file__).parent
source=root/'P4AOriginalFull87ChangedFrontierBudget.lean'
sha=hashlib.sha256(source.read_bytes()).hexdigest()
results={'finite_synthetic_cases':CASES,'python_exact':True,'lean_compiled':False,
         'original_archive_replayed':False,'source_sha256':sha,
         'limits':'Synthetic finite regression; does not validate Lean declarations or 87 archived boxes'}
(root/'STATIC_QA.json').write_text(json.dumps(results,indent=2,ensure_ascii=False)+'\n')
print(json.dumps(results,ensure_ascii=False))
