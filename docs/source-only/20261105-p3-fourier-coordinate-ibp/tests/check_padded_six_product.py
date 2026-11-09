#!/usr/bin/env python3
"""Finite ordered-factor/6-unit-padding regression (NOT a Lean/kernel proof)."""
from functools import lru_cache
from math import prod

@lru_cache(None)
def tuples(r, n):
    if r == 0:
        return ((),) if n == 1 else ()
    return tuple((d,) + tail for d in range(1, n + 1) if n % d == 0
                 for tail in tuples(r - 1, n // d))

count = 0
counts = {}
for n in range(1, 81):
    for j in range(3):
        r = 2 * (j + 1)
        for hb in tuples(r, n):
            assert len(hb) == r and prod(hb) == n
            padded = hb + (1,) * (6 - len(hb))
            assert prod(padded) == n
            for i in range(6):
                assert (hb[i] if i < len(hb) else 1) == padded[i]
            count += 1
            counts[r] = counts.get(r, 0) + 1
print("PASS", count, "original ordered tuples, ranks", counts, "n=1..80")
