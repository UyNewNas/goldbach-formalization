"""Independent exact polynomial check, NOT Lean or physical smooth calculus."""
import sympy as s
from itertools import product
x,y=s.symbols('x y')
W=1+2*x-3*y+5*x*y+7*x**2*y+11*x*y**2
Di=s.diff(W,x); Dj=s.diff(W,y); Dji=s.diff(Di,y)
# Three child shapes are algebraic examples, not true C-infinity cutoff profiles.
F=[lambda t: t**3+2*t+1, lambda t: 2*t**2-t+3, lambda t:t**4-3*t**2+2]
checks=0
for ki,kj in [(0,0),(1,0),(1,2),(2,1)]:
 for ai,aj in product(range(3),repeat=2):
  fi=s.diff(F[ai](x),x,ki); fj=s.diff(F[aj](y),y,kj)
  fi1=s.diff(fi,x); fj1=s.diff(fj,y)
  original=s.diff(W*fi*fj,x,y)
  four=Dji*fi*fj+Di*fi*fj1+Dj*fi1*fj+W*fi1*fj1
  assert s.expand(original-four)==0
  previous=Di*fi*fj + W*fi1*fj
  assert s.expand(s.diff(previous,y)-four)==0
  checks+=2
for child in product(range(3),repeat=6):
 for a,b in [(-1,0),(0,0),(1,2)]:
  untouched=s.prod(F[child[i]](s.Integer(i-2)) for i in [0,2,3,5])
  fi=F[child[1]](x);fj=F[child[4]](y)
  original=s.diff(W*fi*fj,x,y)*untouched
  formula=(Dji*fi*fj+Di*fi*s.diff(fj,y)+Dj*s.diff(fi,x)*fj+W*s.diff(fi,x)*s.diff(fj,y))*untouched
  assert s.simplify((original-formula).subs({x:a,y:b}))==0
  checks+=1
print(f'PASS exact checks={checks}; original six positions, 729 child labels, nonseparable W; POLYNOMIAL SURROGATE ONLY')
