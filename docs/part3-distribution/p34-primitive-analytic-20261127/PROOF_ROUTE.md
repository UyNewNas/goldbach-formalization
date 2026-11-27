# Mathematical route of the existing analytic supplier

This note describes the existing three-module proof and its exact domain. Formal
acceptance is determined by the compiler, replay and inventory receipt, not by
this explanatory note.

## Real lattice domination

For real t > 1 the first module uses the literal summand

`seed t z (c,d) = Im(z)^t * norm(c*z+d)^(-2*t)`.

On a bounded vertical strip with a positive lower height and an upper height,
the existing upper-half-plane estimate bounds this by a constant times
`norm(c,d)^(-2*t)`. The lattice majorant is summable because `2 < 2*t`.
Restriction to the actual primitive pairs preserves summability. A compact
subset of the upper half plane lies in such a strip and has a bounded height,
giving locally uniform convergence of the actual finite-subset sum net.

The all-pairs estimate permits the zero lattice vector; its term is zero in
the convergence range used here. The proof does not assert that its term is
zero at arbitrary exponents such as t = 0. Primitive pairs exclude the zero
vector through their actual gcd condition.

## Complex parameter and the two neighboring exponents

For a primitive pair, let `q = Im(z) / norm(c*z+d)^2`. The actual linear form
is nonzero, so q is positive. The complex seed is literally
`exp(s * log(q))`; its norm is `q^(Re(s))`, which the exact real-power bridge
identifies with the original real seed. Its derivative is
`log(q) * exp(s * log(q))`.

For `a <= Re(s) <= b` and positive epsilon, the proof establishes

`abs(log(q)) * q^(Re(s)) <= (q^(a-epsilon) + q^(b+epsilon)) / epsilon`.

The branch q <= 1 uses the lower neighboring exponent, and the branch q > 1
uses the upper one. Both cases are necessary: the positive quotient is not
globally at most one. Requiring `a-epsilon > 1` and `b+epsilon > 1` makes the
right side a sum of two already convergent real-seed families.

At any s with Re(s) > 1, the proof takes `r = (Re(s)-1)/4`,
`a = Re(s)-r`, `b = Re(s)+r` and `epsilon = r`. The complex ball of radius r
lies in the controlled slab. Both neighboring exponents remain strictly above
one. The supplied summable derivative majorant permits differentiating the
actual primitive infinite sum. The factor `1/2` then gives exactly the
derivative of the original oriented-pair-normalized Eisenstein series.
Differentiability on the open initial half plane supplies `AnalyticOnNhd`.

## The actual period-one Fourier integral

The last module fixes y > 0 and evaluates the preceding objects at `x + i*y`.
On the actual integration set `(0,1]`, the same strip estimate gives an
x-independent summable lattice majorant. The derivative majorant additionally
controls all parameters in the small complex ball. Its sum is a finite real
constant, hence an integrable bound on the finite interval.

The Fourier multiplier is the literal `exp(-2*pi*i*n*x)`, of norm one for
every signed integer n. It preserves both norm bounds. The measurable infinite
integrand, its actual derivative and their integrability are supplied inside
the proof. The pinned dominated derivative theorem then differentiates the
integral with respect to s. Rewriting the restricted-volume integral as the
original interval integral produces the asserted derivative of
`actualPrimitiveFourier y hy n`.

Thus the endpoint is the actual left-hand Fourier integral and its complex
analyticity for fixed positive height, every integer frequency and Re(s)>1.
It does not evaluate a Fourier-K right-hand series or continue either side to
the critical line. Those independent suppliers and all-level/spectral
normalization boundaries remain as listed in SOURCE_SCOPE.md.
