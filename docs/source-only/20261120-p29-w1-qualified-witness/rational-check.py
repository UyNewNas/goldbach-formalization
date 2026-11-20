from fractions import Fraction as F
nu, low, high = F(49,100), F(21,200), F(11,100)
Lmin, Lmax = nu-high, nu-low
assert F(1,5) < low/nu < high/nu < F(1,3)
assert 0 < F(2999,10000)*Lmin-high
assert Lmin == F(19,50) and Lmax == F(77,200)
print('u_low=', low/nu, 'u_high=', high/nu)
print('Lmin=', Lmin, 'Lmax=', Lmax, 'ceiling_slack=', F(2999,10000)*Lmin-high)
