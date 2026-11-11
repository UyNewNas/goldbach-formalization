from fractions import Fraction as Q
from itertools import product
from math import factorial

# Exact polynomial model of an ORIGINAL ordered six-position HB child.
# The geometry W(t) is nonconstant; F_i is differentiated at its actual order.
# This is NOT a Lean / C-infinity / W_T / Lebesgue-integrability proof.
def derivative(coeff, x, n=1):
    return sum((c * Q(factorial(j), factorial(j-n)) * x**(j-n)
                for j, c in enumerate(coeff) if j >= n), Q(0))

def mul(a, b):
    out = [Q(0)] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i+j] += x*y
    return out

checks = 0
for order in [(0,0,0,0,0,0), (1,0,2,1,0,1), (2,1,0,2,1,0)]:
    for i in range(6):
        for labels in product(range(3), repeat=6):
            other = Q(1)
            t = Q(2,5)
            for j in range(6):
                if j != i:
                    a = labels[j]
                    other *= derivative(
                        [Q(a+1), Q(1,a+2), Q(a+3,5), Q(1,7)],
                        Q(j+1,9), order[j])
            a = labels[i]
            F = [Q(a+1), Q(1,a+2), Q(a+3,5), Q(1,7)]
            Fk = [c * Q(factorial(j), factorial(j-order[i]))
                  for j,c in enumerate(F) if j >= order[i]]
            W = [Q(1), Q(i+1,3), Q(1,7)]
            direct = derivative(mul(W,Fk),t) * other
            rhs = (derivative(W,t)*derivative(F,t,order[i]) +
                   derivative(W,t,0)*derivative(F,t,order[i]+1)) * other
            assert direct == rhs, (order, i, labels, direct, rhs)
            checks += 1
print(f"PASS exact polynomial coupled axis derivative {checks}/{checks}, "
      "3 orders x 6 axes x 729 labels")
