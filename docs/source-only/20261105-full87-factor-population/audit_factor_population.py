#!/usr/bin/env python3
"""Independent finite-model checks for P1.4 factor-population packet.

These are NOT Lean checks, archive replay, or validation of the 87-domain geometry.
"""
from fractions import Fraction
from functools import lru_cache
from random import Random

@lru_cache(None)
def primes(n):
    return tuple(p for p in range(2, n + 1) if all(p % k for k in range(2, int(p**0.5) + 1)))

@lru_cache(None)
def factors(n):
    if not n:
        return ()
    a = []
    x = n
    p = 2
    while p * p <= x:
        if x % p == 0:
            a.append(p)
            while x % p == 0:
                x //= p
        p += 1 if p == 2 else 2
    if x > 1:
        a.append(x)
    return tuple(a)

def totient(n):
    if n == 0:
        return 0
    z = n
    for p in factors(n):
        z = (z // p) * (p - 1)
    return z

def factor_cap(N, d):
    return len(primes(N)) if d == 0 else min(len(primes(N)), len(factors(d)))

def main():
    rng = Random(20261105)
    pointwise = 0
    signed = 0
    for N in range(80):
        prefix = primes(N)
        for d in list(range(170)) + [rng.randrange(1, 10**8) for _ in range(30)]:
            count = sum(d % p == 0 for p in prefix)
            cap = factor_cap(N, d)
            assert count <= cap <= len(prefix), (N, d, count, cap)
            if d:
                assert count == sum(p <= N for p in factors(d))
                if d <= N:
                    assert count == len(factors(d))
            else:
                assert count == len(prefix)
            g = Fraction(1, totient(d)) if totient(d) else Fraction(0)
            assert count * g <= cap * g <= len(prefix) * g
            pointwise += 1
    # These tests preserve repeated occurrences, arbitrary signed leaf coefficients
    # and independent nonnegative beta factors; no monotonicity in sieve level.
    for i in range(2500):
        N = rng.randrange(2, 80)
        ds = [rng.randrange(0, 1200) for _ in range(rng.randrange(1, 11))]
        signed_coefs = [Fraction(rng.randrange(-6, 7), rng.randrange(1, 9)) for _ in ds]
        positive_leaf_weights = [Fraction(rng.randrange(0, 8), rng.randrange(1, 11)) for _ in ds]
        value = Fraction(0)
        new_envelope = Fraction(0)
        old_envelope = Fraction(0)
        for d, alpha, beta in zip(ds, signed_coefs, positive_leaf_weights):
            den = totient(d)
            g = Fraction(1, den) if den else Fraction(0)
            count = sum(d % p == 0 for p in primes(N))
            value += alpha * beta * count * g
            new_envelope += abs(alpha) * beta * factor_cap(N, d) * g
            old_envelope += abs(alpha) * beta * len(primes(N)) * g
        assert abs(value) <= new_envelope <= old_envelope, (i, value, new_envelope, old_envelope)
        signed += 1
    print(f'PASS exact pointwise factor/totalized-boundary cases={pointwise}; signed envelope cases={signed}; original87_replay=false; lean_compiled=false')

if __name__ == '__main__':
    main()
