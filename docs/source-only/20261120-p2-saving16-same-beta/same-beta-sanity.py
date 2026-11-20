from fractions import Fraction as F
count=0
for v in [F(1,100),F(1,50),F(1,8),F(3,8),F(5,4)]:
    nu=F(19,96)/v
    for j in range(9,101):
        beta=F(1,j)
        if beta>=F(1,8) or beta*beta>=v: continue
        omega=nu*beta*beta
        assert 0<omega<nu*beta
        assert omega<F(19,96)
        count+=1
print('exact-rational parameter checks:', count, 'verify 0<nu*beta^2<nu*beta and <19/96')
