from fractions import Fraction as F
from itertools import product
for old, fresh in product((False, True), repeat=2):
    for beta, g in ((F(-3, 5), F(7, 11)), (F(0), F(7, 11)), (F(2, 3), F(0))):
        mu = -1
        original = ((mu if fresh else 0) - (mu if old else 0)) * beta * g
        compiler = beta * g
        switch = int(old) - int(fresh)
        assert original == switch * beta * g
        assert original - compiler == (switch - 1) * beta * g
        if beta * g:
            assert (original == compiler) == (old and not fresh)
print('12 synthetic sign cases passed; no Lean elaboration or PP claim')
