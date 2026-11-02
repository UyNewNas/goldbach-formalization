# J / spectral_exceptional: actual exceptional K transform payment

Status: **local analytic transform step written; full exceptional Eq24 OPEN; uncompiled; kernel_verified=false; formal_credit=0**. This is author static inspection, not independent review. Only this assigned J directory was written. No compiler, Lean/lake/build, CI, finite certificate replay, Git operation, quota call or subagent was used.

The delivered step replaces the exceptional real-order K adapter's unusable small-argument bound `exp(8/a)` by an order-sensitive power/log bound, applies it to the existing physical test integral, splits its squared weight at the actual A/J thresholds, and pays finite Fourier smoothing from the existing actual normalized-F derivative theorem. No exceptional spectral mean, Eq24, medium estimate or final polynomial is assumed.

## Original source and newer production dependencies

Read `manuscript-body.tex:116–255`, especially the original medium ranges at 127–156, actual retained phase at 197–210, and precise spectral restrictions at 238–252. Its raw SHA256 remains `ee6aecc164cc59f2d1fed1ad9e48f18f98472ab1d77ab425d53d93bc41ce56bd`. Read the detailed medium module at 299–405 and 454–484, the full final classical-input correspondence, the full fixed-d ABL applicability audit, and the H/I predecessor REGISTRY/REPORT files. H supplies the counted polynomial, not its physical spectral return; I supplies the separate m=0 branch. Neither is reproved here.

The newer production `Part3ActualKAbelSmallArgumentBound.lean` already proves the literal complex-order Abel-normalized small-q bound. This delivery consumes that theorem. It also consumes the actual q=1 moment decay from `Part3GeneralKRightEndpoint.lean`. It does not repeat the older zero-order logarithmic argument or invent a fresh small-q input.

The actual consumer is `ActualRealOrderKPacketAdapterSourceOnly.realOrderTestTransform`, built from the same `spectralTest k Y q` and literal `realOrderK alpha q / q` as the existing packet. The support is the existing `[Y/16,16Y]`; its Lebesgue measure is exactly `(255/16)*Y`. The theorem uses that measure and the actual test's proved norm at most one. The `completedPacketSum`, coprime transformed coefficient, signed cusp branch, every finite row/n carrier, and the single completed interval and phase are preserved.

The current Gamma0 Friedrichs scalar moments, actual all-index physical Hecke coefficient theorem, and radial KL native form-domain theorem were inspected. They are distinct objects. This delivery does not identify radial KL Plancherel with normalized automorphic Kuznetsov, does not infer an exceptional basis or Fourier coefficient normalization from scalar spectral moments, and does not infer a Kim–Sarnak bound for an arbitrary real number.

## Quantitative results

Write `theta=7/32` and

```
ell(q) = 1 + log(2) + max(0,-log(q)),
B(q,alpha) = 2*2^theta*ell(q)*(1+1/q)^|alpha|/(1+q),
G(Y) = 8160*2^theta*16^theta*ell(Y/16)/(1+Y).
```

The first module proves, for every `q>0` and `|alpha|<=theta`,

```
|realOrderK(alpha,q)| <= B(q,alpha).
```

For `q<=1`, it removes the already-proved Abel factor `(q/2)^|alpha|` exactly; real-power inversion also covers `alpha=0`. For `q>=1`, the old general-order moment bound is converted using the newly proved identity `momentMass(0,alpha)=realOrderK(alpha,1)`. The existing small-q bound at q=1 makes that mass uniform in alpha; `(1+q)*exp(1-q)<=2` supplies global decay. Thus there is no uncontrolled constant as alpha approaches zero. Monotonicity of B in the positive argument is proved and used on the physical support.

The second module proves

```
norm(realOrderTestTransform(P,k,alpha))
  <= 255*B(P.Y0/16,alpha)
  <= G(P.Y0)*(1+1/P.Y0)^|alpha|.
```

The factor 255 is the exact support-length/reciprocal-q cancellation. The factor 8160 in G is `255*2*16`; the extra `16^theta` pays the lower endpoint in the exceptional power. This bound is uniform in k and in every packet label. Its existing common-order mode integral is bounded by this same expression times `norm(completedPacketSum(P,k))`; no bound on that remaining coefficient is assumed.

For the physical scale

```
Y = 4*pi*sqrt(A*V*U)/(C*sqrt(Z)), L=U/nu,
X0 = 1+Z/L, T=max(V,Z^2/V),
R = 2/T + 8*C^2*Z/(16*pi^2*A*nu*(L+Z)*(V+Z)^2),
```

the actual squared transform satisfies

```
norm(T_K(k,tau(lambda)))^2
  <= G(Y)^2 * X0^tau(lambda) * max(1,R^theta) * T^tau(lambda),
```

conditionally on the explicit eigenvalue inequality `975/4096<=lambda`. The source theorem converting this inequality to `tau(lambda)<=7/32` is reused. The new internal split is the elementary but source-connected inequality

```
((1+X)^tau)^2 <= X0^tau * ((1+X/sqrt(X0))^2)^tau,
```

followed by the existing exact threshold-ratio theorem. The full `16*pi^2` remains. `physicalScalePacket` inserts the literal Y and `rho=V*D/C`; its consumer needs no caller-supplied Y identity or U=nu*L identity. Its completed interval/phase and completed coefficient sum are definitionally unchanged. This insertion does not claim the missing original-to-automorphic packet dictionary.

The third module also bounds the literal opposite-sign transform normalization `(4/pi)*cos(pi*alpha/2)*T_K` by `(4/pi)*G(Y)*(1+1/Y)^|alpha|`. It does not declare that expression equal to an as-yet-unsupplied automorphic spectral coefficient.

For any finite Fourier set K, the final finite theorem concerns the actual sum

```
sum_(k in K) actualCoeff(rho,sigma,k)
  * integral_q realOrderModeFunction(P,commonRealOrder(alpha),k,q).
```

Its squared norm is bounded by

```
[G(Y)*(1+1/Y)^|alpha|]^2 * actualW(rho,sigma,0)
  * sum_(k in K) norm(actualCoeff(rho,sigma,k))*norm(completedPacketSum(P,k))^2.
```

The last factor is an explicitly defined `finiteCompletedEnergy`. It is not assumed small. The actual Fourier l1 norm is supplied by the existing derivative/separation theorem. With `V<=x^eta*C/D`, `D>0`, `x>=1`, `eta>=0`, and `|sigma|<=1`, a constant selected first replaces `actualW` by `B*x^(12*eta)`. No retained five-coordinate phase charge is inserted again. The remaining spectral coefficient energy retains its Fourier weights; it has not been replaced by a count norm or by a spectral theorem.

## Foundational statement audit and quantifier boundary

The primary [Pascadi v3 text](https://arxiv.org/html/2404.04239v3) was read at Theorems A, C, J, (3.18), and Lemma D. A permits arbitrary complex coefficients at one level, `L>=1/2`, cusp density `1/z`, with weight range `max(1,z/L,z^2/L^3)`. J requires one phase across levels, infinity scaling Id, `V,Z>=1/2`, and range `max(V,Z^2/V)`. Its common partial-interval extension still needs finite Fourier completion. C gives the half-parameter cap 7/64, hence doubled cap 7/32. Our opposite-sign factor matches (3.18). The new `fixed_level_A_range` proves the factor-two inclusion of `1+Z/L` when `z>=Z`. These are audited pending interfaces, not new Lean assumptions supplying A, J or Eq24.

The original `c0`, sigma, kappa and moving-residue hypotheses are unchanged. The local transform estimate is uniform on all positive physical scales, so it requires no extra c0 or sigma condition. Its finite smoothing constant precedes every packet, A, C, D, x, eta, alpha and Fourier set. Converting its explicit logarithmic scale cost and smoothing exponent into the original single common threshold remains separate. The `lambda` lower bound is conditional and does not assert an actual automorphic instance.

## Remaining exact obligations

1. The actual nonzero-frequency Poisson source must be identified with the normalized automorphic Kuznetsov expansion, with the physical cusp conversion, signed coefficients, common m interval, and the exact retained c-unit gates. The present packet adapter is genuine smooth/Fourier data but contains no automorphic Fourier factors; its completed coefficient energy cannot be passed directly to A or J.
2. The positive-sign exceptional J-Bessel transform and its normalization are not covered by the K bound. The delivered formula is the opposite-sign K transform; no equality between those two signs is claimed.
3. The actual automorphic exceptional spectrum must have the Kim–Sarnak instance and normalized Fourier coefficients. The A/J norms, cusp density/scaling, and nonempty length conditions must then be instantiated. `PacketData.m_normalized` only gives its existing fixed box; it is not a proof of a dyadic `(V,2V]` carrier or `V>=1/2`.
4. The coprime ABL oldform packet transformation remains required: `(a,z)=1`, common height-independent `1_(n,a)=1 beta(nu*n,z)e(-n/z)`, and dilation-dependent multipliers handled by packet norms. The current finite Hecke expression theorem is not this packet theorem. Cancellation of the `(A*nu)^theta` factor in the improved exceptional term is still unproved on actual spectral sums.
5. Common partial-interval Fourier completion for J, level Cauchy, the actual auxiliary nu source and subpower sum, passage from finite Fourier mode sets to the complete automorphic spectral sum, and the log(Y)/original-scale subpower payment remain. The theorem here retains the finite coefficient energy explicitly.
6. The full Eq24 exceptional return, attachment to the existing exceptional Eq24-to-Eq25 algebra and H counted polynomial, complete source dictionary, two square roots, E2/dispersion and full medium conclusion remain OPEN. Separate m=0 and y=0 work is untouched.

No mathematical contradiction with the manuscript was found. This delivery removes a real quantitative transform/smoothing obstruction; it does not close the yellow uniform-spectral leaf.

## Source-only installation and checks

Install the three new files under the matching `ImbalancedChen.<stem>` names in the order GlobalBudget, PacketBudget, PhysicalNormalization. Production dependencies were read at their current exact paths, including newer production proof proposals. REGISTRY records their raw hashes, import lists, declaration names and actual install status. H/I source-only predecessors are recorded as reference pins, not falsely claimed installed imports.

Only text inspection, primary-source reads, ordinary file existence checks and raw SHA256 inventory were used. Forbidden-placeholder/axiom/decision-command text search found none in the three candidate files. No elaboration, compiler or kernel check was run. Independent Astra review and user-owned strict Lean checking remain required. The broad task is incomplete and earns zero formal credit.
