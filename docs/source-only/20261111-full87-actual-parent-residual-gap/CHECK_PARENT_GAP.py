#!/usr/bin/env python3
"""Finite rational sanity checks ONLY, not a Lean elaboration or original-source replay."""
from fractions import Fraction as Q
from random import Random
from pathlib import Path
import re

cutoff = Q(53, 13824)
rand = Random(20261111)
for i in range(10000):
    S = Q(rand.randint(1, 400), 200)
    P = S + cutoff + Q(rand.randint(0, 100000), 10000)
    R = P + Q(rand.randint(0, 10000), 10000)
    M = R + Q(rand.randint(1, 1000), 10000)
    J = cutoff**8 + Q(rand.randint(0, 10000), 10000)
    def res(x):
        return 4*(M-x)/((x-S)*(M-S)*J)
    gap = res(P) - res(R)
    exact = 4*(R-P)/((P-S)*(R-S)*J)
    assert gap == exact, ('identity',i)
    assert 0 <= gap <= 4*(R-P)/cutoff**10, ('bounds',i)
    # M is rounded down from an ideal larger M0; rounding has a distinct sign.
    M0 = M+Q(rand.randint(0,100),10000)
    real = res(P)
    ideal = 4*(M0-R)/((R-S)*(M0-S)*J)
    rounded = res(R)
    assert real <= ideal + 4*(R-P)/cutoff**10, ('two_sided_upper',i)
    assert ideal - (ideal-rounded) <= real, ('two_sided_lower',i)

s=Path(__file__).with_name('P4AOriginalFull87ActualParentResidualGap.lean').read_text()
for t in ('sorry','admit','native_decide','unsafe','axiom'):
    assert not re.search(r'\b'+t+r'\b',s),t
for op,cl in [('(',')'),('[',']'),('{','}')]:
    assert s.count(op)==s.count(cl),(op,s.count(op),s.count(cl))
print('10000 exact Fraction residual-parent-gap + signed-boundary checks passed; 0 violations')
print('Static proof-escape token and basic delimiter checks passed; NOT Lean checked')
