"""VE-only exact source excerpts; see source_manifest.json for provenance."""


from fractions import Fraction as F


def ceildiv(n, d):
    assert d > 0
    return -((-n) // d)


THETA = F(299, 500)


MU = F(25, 128)


DEN = 48000 * 2**24


def v_lo(lo,hi):
    return min((DEN+lo)//2,(57*DEN-96*hi)//64)


def v_point_hi(t):
    return min(ceildiv(DEN+t,2),ceildiv(57*DEN-96*t,64))


def v_hi(lo,hi):
    if lo<=NMU<=hi:
        return ceildiv(153*DEN,256)
    return max(v_point_hi(lo),v_point_hi(hi))


def phi_range(cell):
    """Range enclosure of the exact reduced full envelope on ordered points.

    For 0<=z<=y<=x<=mu, the middle affine piece of v is redundant,
    w1's inner minimum is B(z)=153/256-3*z/8, and w2 is dominated.
    Each pair gate is automatically satisfied by at least 3/256 whenever
    v(pair)>=v(x): for pair s<=mu use 1/2-5*mu/2; for s>=mu,
    v(s)>=v(x) implies s<=(25/32-x)/3 and hence
    v(s)-(s+2*x)>=23/96-7*x/6>=3/256. Thus pair gates can be removed
    inside the max with v(x). Formula bounds are evaluated on a rectangle,
    but are needed only on its ordered subset.
    """
    x0,x1,y0,y1,z0,z1=cell
    # Initial x intervals are split at mu and subdivision preserves this.
    # On an ordered point with x>mu, use only v(x). On a symmetric square
    # above mu, extend it as v(max(x,y)); its range is the same interval.
    assert x1<=NMU or x0>=NMU
    if x0>=NMU:
        return min(NT,v_lo(x0,x1)),min(NT,v_hi(x0,x1))
    branches=[(x0,x1),(y0,y1),(x0+y0,x1+y1),(x0+y0+z0,x1+y1+z1),
              (x0+z0,x1+z1),(y0+z0,y1+z1)]
    low=max(v_lo(a,b) for a,b in branches)
    high=max(v_hi(a,b) for a,b in branches)
    low=max(low,(153*DEN-96*z1)//256)
    high=max(high,ceildiv(153*DEN-96*z0,256))
    return min(NT,low),min(NT,high)
