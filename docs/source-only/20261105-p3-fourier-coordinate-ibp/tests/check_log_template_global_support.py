#!/usr/bin/env python3
"""Finite independent regression for P3.6 global support of genuine smooth
HB three-way log templates. This is NOT Lean, a general C-infinity proof,
or a numerical certification of Fourier L1/H or PP."""
from mpmath import mp
mp.dps = 60

def switch(z):
    return mp.exp(-1 / z) if z > 0 else mp.mpf("0")

def chi(t):
    if t <= 1:
        return mp.mpf("1")
    if t >= 2:
        return mp.mpf("0")
    a, b = switch(2 - t), switch(t - 1)
    return a / (a + b)

def gate(t, a):
    if a == 0:
        return chi(4 * t - 2)
    if a == 1:
        return chi(4 * t - 3) - chi(4 * t - 2)
    return 1 - chi(4 * t - 3)

def child(u, a):
    t = mp.exp(u)
    return (chi(t) - chi(2 * t)) * gate(t, a)

def scaled(v, j, a):
    x = mp.power(2, j) * mp.exp(v)
    t = x / mp.power(2, j)
    return (chi(t) - chi(2 * t)) * gate(t, a)

checks = 0
orders = (0, 1, 2, 3)
exterior = (-3, -2, -1, -mp.log(2) - mp.mpf("0.1"),
            mp.log(2) + mp.mpf("0.1"), 1, 2, 3)
for a in range(3):
    for k in orders:
        for u in exterior:
            v = mp.diff(lambda x: child(x, a), u, k)
            assert v == 0, (a, k, str(u), str(v))
            checks += 1
    for u in (-mp.mpf("0.45"), -mp.mpf("0.2"), mp.mpf("0.08"),
              mp.mpf("0.31"), mp.mpf("0.58")):
        for j in (0, 2, 6, 17, 37):
            for k in orders:
                a1 = mp.diff(lambda x: child(x, a), u, k)
                a2 = mp.diff(lambda x: scaled(x, j, a), u, k)
                assert abs(a1 - a2) < mp.mpf("1e-45") * (1 + abs(a1))
                checks += 1

print(f"PASS {checks}/{checks} finite cases; exterior derivative k=0..3 zero "
      "on the explicit smooth cutoff, sampled scale invariance")
