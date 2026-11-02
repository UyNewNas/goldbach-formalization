# K / exceptional_j: normalized positive J cancellation and the small physical packet

**Local source step written; full task and P3.5.uniform_spectral remain OPEN.** This is an author static inspection, pending independent review. All three Lean candidates are uncompiled: `compiled=false`, `kernel_verified=false`, `formal_credit=0`. The quantitative transform theorem has the explicit gate `Y<=1/16`; no all-scale transform estimate is claimed.

The new work proves a uniform, order-sensitive bound for the actual normalized positive-sign J kernel, including its removable value at order zero. It attaches that kernel to the unchanged physical packet, proves exact Fourier reconstruction, and derives its small-scale transform, physical A/J weight split and finite smoothing estimate. No J-kernel bound, Eq24, bare spectral norm, A/J estimate or ABL cancellation is assumed.

## Original source and predecessor comparison

Read the K README and exact `exceptional_j` assignment; J's complete report/registry and current independent review; original `manuscript-body.tex:116-255`; medium-completion lines 299-405 and 454-484; the complete classical-input correspondence and fixed-d ABL audit. The manuscript has raw SHA256 `ee6aecc164cc59f2d1fed1ad9e48f18f98472ab1d77ab425d53d93bc41ce56bd`. Original `c=49044063/25000000` and `K=8452171/1250000` are unchanged and unused by this local special-function step.

J's exact predecessor registry pin is `e9ce6e9060125b30efd04474bfd757cb81f99f02ae7c276998dda491da075bb2`. Its independent verdict is `SOURCE_REVIEW_PASS_FOR_EXCEPTIONAL_K_TRANSFORM_AND_FINITE_SMOOTHING_ONLY`. Its K transform and finite smoothing are source candidates, not kernel-certified proofs or a completed exceptional spectral return. The new code imports the recorded J draft `Part3ActualExceptionalPhysicalNormalization`, together with its recorded draft dependencies; their production installation targets remain absent.

Newer production already supplies actual ordinary `generalJ` through the literal alternating Gamma series, its symmetric Poisson representation, genuine order holomorphy on `Re(nu)>-1/4`, the actual order derivative, its first q derivative, compact real-order Poisson weight continuity, and the removable critical quotient. These were read and reused. The existing uniform real-order bound `q^(-r)` at one fixed radius r does not retain the individual exceptional power needed here. The new derivative estimate works on every shrinking interval `[-alpha,alpha]`, with one constant chosen before alpha.

The saved primary Pascadi v3 extraction was read at (3.18), Lemma D, Theorems A/C/J, and the defining spectral parameter convention. The live web tool failed to connect; the local TeX-preserving primary extraction and its companion provenance are pinned. The normalization used is the literal positive transform from [Pascadi (3.18)](https://arxiv.org/html/2404.04239v3), with no use of Lemma D as a Lean estimate premise. Available Mathlib source was read directly at the recorded read-only WSL path, and selected APIs were also read at the manifest-pinned GitHub revision. No package was installed or built.

## Actual kernel and cancellation

For doubled exceptional order `0<=alpha<=theta=7/32`, define

```
H_alpha(q) = pi/(2*sin(pi*alpha/2)) * (J_alpha(q)-J_(-alpha)(q)), alpha!=0,
H_0(q)     = 2 * actualJOrderDerivative(0,q).
```

The code proves, for q>0, that this is `-(pi/2)*criticalJRealKernel(q,i*alpha/2)`. For alpha>0 it also proves the literal `(pi/sinh(pi*r))*(J_(2ir)-J_(-2ir))/(2i)` identity at `r=i*alpha/2`. Thus the factors pi, 2, i and the exceptional sign are explicit. The value at zero follows the already-proved analytic removable quotient; it is not totalized division by zero. This is a special-function identity, not an identification with an automorphic expansion.

The main new internal estimate is

```
exists D>0, forall 0<=a<=theta, |nu|<=a, 0<q<=1,
  norm(actualJOrderDerivative(nu,q)) <= D*(1+abs(log q))*q^(-a).
```

Its proof bounds the actual reciprocal Gamma factor and its native derivative on the fixed compact order band. One integrable Poisson weight of order -3/8 dominates the ordinary Poisson integral; the already-proved logarithmic endpoint envelope dominates the differentiated integral. The positive principal power is bounded by `2^theta*q^(-a)`, preserving the radius a of the current segment. The actual differentiated Poisson/Gamma formula supplies the displayed derivative estimate.

The real mean-value theorem on `[-alpha,alpha]` then bounds the actual numerator by `2*alpha*D*(1+abs(log q))*q^(-alpha)`. Jordan's inequality gives `sin(pi*alpha/2)>=alpha`. The factors alpha cancel before division, and the zero branch is handled by its actual derivative value. Consequently one fixed `B>0`, independent of alpha and q, satisfies

```
norm(H_alpha(q)) <= B*(1+abs(log q))*q^(-alpha),  0<q<=1.
```

`smallKernelConstant` is chosen from this proved existence theorem. It is not a structure field containing a requested estimate. No pointwise order-dependent `1/alpha` constant remains.

## Original physical source and the proved scale range

`withPositiveKernel` changes only the original `PacketData.kernel` to a continuous extension of `H_alpha(q)/q` below the physical region. The extension agrees with that literal kernel everywhere on `[Y/16,16Y]`. Positive-q continuity is proved also at alpha=0 using the existing native mixed derivative theorem. The following remain literal: `normalizedF(rho,sigma)`, every row and n carrier, signed cusp coefficient, `modePacket`, the single `Finset.Ico(lo,hi)` completed interval, and phase `k1/(64V)`.

The adapter proves equality with `positivePhysical`, an explicit sum of the original normalized F atoms multiplied by `H_alpha(q)/q`; proves its integrability; proves exact mode factorization; and consumes the original Fourier reconstruction theorem to obtain

```
HasSum (k => actualCoeff(rho,sigma,k)*T_J(P,k,alpha)*completedPacketSum(P,k))
       (integral positivePhysical(P,alpha)).
```

This all-mode reconstruction and integrability hold at every positive Y. They do not supply automorphic Fourier coefficients or a Kuznetsov formula.

For the quantitative bound the explicit gate `Y<=1/16` ensures the full physical support lies in `0<q<=1`. The proved test norm is at most one. The exact support length `(255/16)*Y` cancels the reciprocal lower endpoint `Y/16`, giving

```
norm(T_J) <= 255*B*(1+abs(log(Y/16)))*(Y/16)^(-alpha)
          <= G_J(Y)*(1+1/Y)^alpha,
G_J(Y) = 510*B*16^theta*(1+abs(log(Y/16)))/(1+Y).
```

The second inequality retains the individual exponent alpha and pays only `16^theta` for the endpoint change. The factor 2 restores the standard denominator in this small-scale range. This is not a claim of oscillatory decay for large Y.

Using J's unchanged `physicalScalePacket`, the source scale is exactly

```
Y = 4*pi*sqrt(A*V*U)/(C*sqrt(Z)), rho=V*D/C, L=U/nu.
```

The new `physical_small_scale_iff` proves that the scale gate is exactly `4096*pi^2*A*V*U <= C^2*Z` for positive scales. Thus it is an explicit restriction on the original source region, not a substituted test or an asserted covering of all packets.

For `tau=tau(lambda)` with the explicit conditional hypothesis `lambda>=975/4096`, the existing exact threshold algebra gives

```
norm(T_J)^2 <= G_J(Y)^2 * (1+Z/L)^tau
               * max(1,ratioBound(A,nu,L,V,Z,C)^theta)
               * max(V,Z^2/V)^tau.
```

`ratioBound` retains the original `16*pi^2*A*nu*(L+Z)*(V+Z)^2` denominator. This is the same physical spectral-weight geometry as J's opposite-sign K counterpart, now applied to the normalized positive J transform. It does not instantiate either spectral norm theorem or assert a Kim-Sarnak theorem for arbitrary lambda.

Finally, finite Fourier smoothing is derived with the exact existing `finiteCompletedEnergy`:

```
norm(finiteSeparatedPositiveIntegral)^2
  <= [G_J(Y)*(1+1/Y)^alpha]^2 * actualW(rho,sigma,0)
     * sum_(k in K) norm(actualCoeff(rho,sigma,k))*norm(completedPacketSum(P,k))^2.
```

The actual normalized-F supplier pays `actualW<=B0*x^(12*eta)` from `V<=x^eta*C/D`, `D>0`, `x>=1`, `eta>=0`, and `abs(sigma)<=1`. B0 is selected before every packet, residue, scale, alpha and finite mode set. No second retained five-coordinate phase charge is added. The coefficient energy remains explicit.

## Remaining exact obligations

1. **Large-scale J transform:** derive the required oscillatory profile on `Y>1/16`, including its mode derivative cost and weighted Fourier payment. Neither the present small-q Poisson bound nor the existing bare `J_nu(q)=O(q^-1/2)` bound proves the required integrated large-Y decay. The new scale gate has not been proved for all original packets. Full positive-sign transform control remains OPEN.
2. **Automorphic source:** identify the original nonzero Poisson sum with normalized Kuznetsov at the signed cusp pair, exact cusp modulus `c*sqrt(z)`, physical `4*pi` argument, and true Fourier coefficients. The smooth packet adapter alone does not establish this dictionary.
3. **Actual A/J norms:** supply the actual exceptional spectrum and a genuine Kim-Sarnak instance; fixed-level arbitrary n coefficients with cusp density `1/z` and length at least 1/2; averaged-level J with infinity scaling Id, lengths at least 1/2, one common phase, and common partial-interval Fourier completion. Existing PacketData coordinate boxes do not prove those dyadic-carrier hypotheses.
4. **ABL and cancellation:** prove the coprime oldform packet identity/norm with dilation-dependent Hecke factors, the common height-independent coefficient `1_(n,a)=1 beta(nu*n,z)e(-n/z)`, and cancellation of `(A*nu)^theta` only in the improved exceptional term. None is replaced by a bare norm input or asserted from finite Hecke algebra.
5. **Return assembly:** bound the retained coefficient energy using those genuine spectral norms, justify the full automorphic Fourier/spectral passage and level Cauchy, pay the actual auxiliary-nu sum and the explicit logarithmic scale cost, and attach to Eq24, Eq25/H, the two square roots and E2/full medium. The separate m=0 and y=0 branches are unchanged.
6. Independent source review and user-owned strict Lean elaboration remain required. Imported candidates are not granted inherited kernel credit.

No contradiction with the manuscript was established. The strict candidates remove a real small-argument exceptional J cancellation/source/profile obstruction; they do not close the uniform spectral leaf.

## Installation and verification boundary

Install the three K files at their matching `ImbalancedChen.<stem>` targets, in order SmallKernel, PacketAdapter, SmallPacketBudget, after installing the three pinned J exceptional K/physical modules. REGISTRY records raw hashes, every new direct import, exact current draft locations, production installation status and public declaration names, plus the actual supporting sources and primary references inspected.

Only source text inspection, primary-source/API reads, existence checks and raw metadata hashing were performed. No compiler, Lean/lake/build, CI, finite certificate/decision execution, producer replay, Git operation, quota call or subagent was used. Every shell explicitly selected the workspace. Only this assigned K directory was written.
