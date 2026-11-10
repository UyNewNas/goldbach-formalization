#!/usr/bin/env python3
"""Finite smooth-cutoff log-chart sanity checks; NOT Lean evidence."""
import mpmath as mp
mp.mp.dps = 50
def flat(t): return mp.exp(-1/t) if t > 0 else mp.mpf(0)
def chi(t):
    if t <= 1: return mp.mpf(1)
    if t >= 2: return mp.mpf(0)
    A, B = flat(t-1), flat(2-t)
    return B/(A+B)
def gate(t,a):
    if a == 0: return chi(4*t-2)
    if a == 1: return chi(4*t-3)-chi(4*t-2)
    return 1-chi(4*t-3)
def template(u,a):
    t=mp.exp(u)
    return (chi(t)-chi(2*t))*gate(t,a)
def chart(u,a,j):
    x=mp.power(2,j)*mp.exp(u)
    t=x/mp.power(2,j)
    return (chi(t)-chi(2*t))*gate(t,a)
checks=0
for a in range(3):
    for u0 in [-mp.mpf(".69"),-mp.mpf(".48"),-mp.mpf(".15"),mp.mpf(0),mp.mpf(".13"),mp.mpf(".36"),mp.mpf(".62")]:
        for j in [0,1,3,17,37]:
            for k in range(5):
                v=mp.diff(lambda u:template(u,a),u0,k)
                w=mp.diff(lambda u:chart(u,a,j),u0,k)
                assert abs(v-w)<=mp.mpf("1e-35")*(1+abs(v)), (a,j,k,u0)
                checks+=1
for u in [-mp.mpf(".69"),-mp.mpf(".3"),mp.mpf(0),mp.mpf(".35"),mp.mpf(".69")]:
    assert abs(sum(template(u,a) for a in range(3))-(chi(mp.exp(u))-chi(2*mp.exp(u))))<mp.mpf("1e-40")
    checks+=1
print(f"PASS {checks}/530 finite smooth-cutoff chart/derivative cases, order 0..4, scales through 2^37")
print("No Lean execution; no global numerical derivative upper bound inferred.")
