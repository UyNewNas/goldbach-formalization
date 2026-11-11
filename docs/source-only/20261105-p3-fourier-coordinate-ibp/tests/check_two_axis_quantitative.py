"""Independent finite rational polynomial regression for SOURCE_ONLY P3.6.

These polynomial proxy child functions do NOT model the real C-infinity cutoff,
Lebesgue L1, Lean elaboration or physical W_T. They verify the exact four-term
mixed coordinate Leibniz algebra and the all-3^6-child POINTWISE bound.
"""
from fractions import Fraction
from itertools import product
import sympy as sp

u = sp.symbols('u0:6')
W = 1 + u[0]*u[1] + u[2]*u[3] + u[4]*u[5] + u[0]**2 + u[1]*u[4]
f = [lambda x: 1+x, lambda x: 1-x+x*x, lambda x: 1+x**3]
children = tuple(product(range(3), repeat=6))
points = ((sp.Rational(0),)*6,
          (sp.Rational(1,2), sp.Rational(-1,2), sp.Rational(1,4),
           sp.Rational(0), sp.Rational(-1,4), sp.Rational(1,2)))
C, M0, M1, M2 = (sp.Integer(v) for v in (10, 10, 5, 3))
assert len(children) == 729
norm_checks = 0
exact_checks = 0
for point in points:
    substitutions = dict(zip(u, point))
    w0 = W.subs(substitutions)
    w1 = [sp.diff(W, u[i]).subs(substitutions) for i in range(6)]
    w2 = [[sp.diff(W, u[i], u[j]).subs(substitutions) for j in range(6)] for i in range(6)]
    assert abs(w0) <= M0
    assert all(abs(w1[i]) <= M1 for i in range(6))
    assert all(abs(w2[i][j]) <= M2 for i in range(6) for j in range(6))
    for child in children:
        v = [f[child[k]](u[k]) for k in range(6)]
        x0 = [z.subs(substitutions) for z in v]
        x1 = [sp.diff(v[k], u[k]).subs(substitutions) for k in range(6)]
        x2 = [sp.diff(v[k], u[k], 2).subs(substitutions) for k in range(6)]
        for i,j in product(range(6),repeat=2):
            p0 = sp.prod(x0)
            pi = sp.prod(x1[k] if k==i else x0[k] for k in range(6))
            pj = sp.prod(x1[k] if k==j else x0[k] for k in range(6))
            pij = sp.prod(x2[k] if k==i==j else x1[k] if k in (i,j) else x0[k] for k in range(6))
            formula = w2[i][j]*p0 + w1[i]*pj + w1[j]*pi + w0*pij
            assert abs(formula) <= (M2+2*M1+M0)*C**6
            norm_checks += 1
            if child in children[::120]:
                true_poly = sp.diff(W * sp.prod(v),u[i],u[j])
                assert sp.expand(true_poly - (sp.diff(W,u[i],u[j])*sp.prod(v)
                  + sp.diff(W,u[i])*sp.prod(sp.diff(v[k],u[k]) if k==j else v[k] for k in range(6))
                  + sp.diff(W,u[j])*sp.prod(sp.diff(v[k],u[k]) if k==i else v[k] for k in range(6))
                  + W*sp.prod(sp.diff(v[k],u[k],2) if k==i==j else sp.diff(v[k],u[k]) if k in (i,j) else v[k] for k in range(6)))) == 0
                assert true_poly.subs(substitutions) == formula
                exact_checks += 1
print(f'PASS bound={norm_checks}, exact_symbolic={exact_checks}, children={len(children)}, repeated_axes_included=True')
