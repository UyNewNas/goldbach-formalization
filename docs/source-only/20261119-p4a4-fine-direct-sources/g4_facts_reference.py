"""Fraction-based reference for the 16 original saved-sixth Facts fields."""
from fractions import Fraction as F
from itertools import product

def plus(a,b):return (a[0]+b[0],[a[1][i]+b[1][i] for i in range(6)])
def minus(a,b):return (a[0]-b[0],[a[1][i]-b[1][i] for i in range(6)])
def constant(x):return (F(x),[F(0)]*6)
def coord(i,c=1):return (F(0),[F(c if j==i else 0) for j in range(6)])
def total():return (F(0),[F(1)]*6)
def selected(mask,k=6):return (F(0),[F(1 if j<k and mask>>j&1 else 0) for j in range(6)])
def tent(mask,desc,k=6):
 s=selected(mask,k)
 return (F(57,64),[-F(3,2)*x for x in s[1]]) if desc else (F(1,2),[x/2 for x in s[1]])
def rescue():return (F(153,256),[F(0),F(0),-F(3,8),F(0),F(0),F(0)])
def ev(p,x):return p[0]+sum((p[1][j]*x[j] for j in range(6)),F(0))
def lower(p,lo,hi):return p[0]+sum((p[1][j]*(lo[j] if p[1][j]>=0 else hi[j]) for j in range(6)),F(0))
def upper(p,lo,hi):return p[0]+sum((p[1][j]*(hi[j] if p[1][j]>=0 else lo[j]) for j in range(6)),F(0))
def facts(row):
 grid,*rest=row;L=rest[:6];mask,ds,old,new=rest[6:]
 if grid!=400 or min(L)<8 or L[0]+1>78 or any(L[j+1]+1>L[j] for j in range(5)) or not 32<=mask<64 or old<=0 or new<=0:return False
 lo=[F(x,400) for x in L];hi=[F(x+1,400) for x in L];mid=[(lo[j]+hi[j])/2 for j in range(6)]
 a,d=tent(mask,False),tent(mask,True);h3=plus(plus(coord(0),coord(1)),coord(2,3));h5=plus(plus(plus(plus(coord(0),coord(1)),coord(2)),coord(3)),coord(4,3))
 def above(x,y):return lower(minus(x,y),lo,hi)>=F(1,1600)
 masks=[0,1,3,7,5,6]
 def pairs(j):return (rescue(),rescue()) if j==0 else (tent(masks[j],False,5),tent(masks[j],True,5))
 if not any(all(above(x,h3) for x in pairs(j)) for j in range(6)):return False
 if not any(all(above(x,h5) for x in pairs(j)) for j in range(6)):return False
 if not all(above(x,constant(F(1,2))) for x in (a,d)):return False
 for j in range(6):
  full=(F(0),[F((1 if k<j else 0)+(2 if k==j else 0)) for k in range(6)])
  if not all(above(x,full) for x in (a,d)):return False
  remain=(F(0),[F((1 if mask>>k&1 else 0)+(1 if k<j and not (mask>>k&1) else 0)+(2 if k==j else 0)) for k in range(6)])
  if not(mask>>j&1) and not all(above(x,remain) for x in (a,d)):return False
 if not any(upper(minus(minus(x,total()),coord(5,3)),lo,hi)<=0 for x in (a,d)):return False
 oldfaces=[rescue()]
 for m in range(1,32):
  x,y=tent(m,False,5),tent(m,True,5);xx,yy=ev(x,mid),ev(y,mid)
  oldfaces.append(x if xx<=yy and xx<=F(153,256) else y if yy<=F(153,256) else constant(F(153,256)))
 oldcond=all(upper(minus(x,total()),lo,hi)<=F(old,102400) for x in oldfaces) or any(upper(minus(x,total()),lo,hi)<=F(old,102400) for x in (a,d))
 newcond=any(upper(minus(x,total()),lo,hi)<=F(new,102400) for x in (a,d))
 if not oldcond or not newcond:return False
 s=F(0)
 for bits in product((False,True),repeat=6):
  t=[hi[j] if bits[j] else lo[j] for j in range(6)]
  s+=min(ev(a,t),ev(d,t))-max(ev(x,t) for x in oldfaces)
 return 102400*s==ds
