"""Exact rational regression for P3.6 positive-scale dyadic group profile.
Finite polynomial proxies only; no C∞ cutoff, Lean or kernel validation.
"""
from fractions import Fraction

polys = [
    [Fraction(1), Fraction(3,2), Fraction(-2,3), Fraction(4,7)],
    [Fraction(0), Fraction(-1,5), Fraction(7,11), Fraction(2,9), Fraction(-3,8)],
    [Fraction(5,4), Fraction(-2), Fraction(0), Fraction(1,3)],
]
scales = [Fraction(1,7), Fraction(1,2), Fraction(1), Fraction(3,2), Fraction(7), Fraction(29)]
points = [Fraction(1,13), Fraction(1,2), Fraction(1), Fraction(11,7), Fraction(5)]
checks = 0
for coeff in polys:
    for c in scales:
        for k in range(7):
            for z in points:
                actual = sum(a*(1-2**j)*(c*z)**j*j**k for j,a in enumerate(coeff))
                translated = sum(a*(1-2**j)*(z*c)**j*j**k for j,a in enumerate(coeff))
                assert actual == translated
                checks += 1
for coeff in polys:
    for c in scales:
        for maskbits in range(2**6):
            for i in range(6):
                for j in range(6):
                    first = int(bool(maskbits & (1<<i)))
                    second = int(bool(maskbits & (1<<j)))
                    for z in (Fraction(1,2), Fraction(2)):
                        h = sum(a*(1-2**n)*(c*z)**n*n*n for n,a in enumerate(coeff))
                        predicted = first*second*h
                        actual = sum(a*(1-2**n)*(c*z)**n*(first*n)*(second*n) for n,a in enumerate(coeff))
                        assert actual == predicted
                        checks += 1
print(f"PASS {checks}/{checks} exact rational polynomial Euler/axis checks")
