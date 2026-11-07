Independent source review of J task `spectral_exceptional`, by `/root/j_review_exceptional`, 2026-11-02.

**Verdict: SOURCE_REVIEW_PASS_FOR_EXCEPTIONAL_K_TRANSFORM_AND_FINITE_SMOOTHING_ONLY.** The three frozen modules supply a substantive local analytic step for the existing real-order K integral and its physical packet. The exceptional Eq24 return and yellow node P3.5.uniform_spectral remain **OPEN**. This review grants no compilation or kernel credit: `compiled=false`, `kernel_verified=false`, `formal_credit=0`, `task_complete=false`.

The reviewed freeze is exact:

| Artifact | Raw SHA256 |
| --- | --- |
| REGISTRY.json | e9ce6e9060125b30efd04474bfd757cb81f99f02ae7c276998dda491da075bb2 |
| REPORT.md | c88e7fb8e8572c6f0b075c9ded8b90dedfa1619c7b6a672b8ee6ec9965ef3ef7 |
| Part3ActualExceptionalKGlobalBudget.lean | 6662faa00da913f2e4a0c430cde139f2b4e3429efad7f35faf29f9b95f3dffc3 |
| Part3ActualExceptionalKPacketBudget.lean | bb53eba83b341adff77925262257b16a92dbb669f7313f67392f95c5acb82cc8 |
| Part3ActualExceptionalPhysicalNormalization.lean | e46e85af17f0e6352dff2860a43ea0cf15115f3def0d67f3dfbd509738c9dd6b |

All 35 explicit source/dependency/reference/report pins in this registry match current raw bytes. All three new direct-import lists match their source text; their production installation targets remain absent as recorded. The 36 registered declaration names agree with the three modules. The audit covers these registered pins and the consumed interfaces, not every recursive import. Hash agreement establishes identity, not mathematical validity.

I read J README and the exact TASKS row; all three new modules; the original manuscript at lines 116-255; medium-completion lines 299-405 and 454-484; the classical correspondence and fixed-d ABL applicability audit; and H medium_variance and I spectral_eq24 registry/report records. H's finite counted polynomial is not a physical spectral bound. I's m=0 branch is separate from the nonzero exceptional return. The existing exceptional Eq24-to-Eq25 module supplies real-power algebra only. None of these predecessors is promoted to a completed Eq24 proof.

The local findings are as follows.

1. **The actual K bound is derived, including order zero.** GlobalBudget lines 44-188 use the existing Abel-normalized complex K theorem at order `|alpha|`, the real-order bridge and evenness, and invert the positive real power `(q/2)^|alpha|`. The large-q proof identifies `momentMass 0 alpha` with the literal positive `realOrderK alpha 1`; it bounds that mass by the small-q theorem at q=1 and uses `(1+q)*exp(1-q)<=2`. Thus for q>0 and `|alpha|<=theta=7/32`, the displayed bound is

   `|K_alpha(q)| <= 2*2^theta*ell(q)*(1+1/q)^|alpha|/(1+q)`,

   where `ell(q)=1+log(2)+max(0,-log(q))`. There is no singular order-dependent constant as alpha tends to zero. Lines 190-215 prove the positive-argument monotonicity needed by the packet. This is new proof work on the actual integral, not a renamed desired estimate.

2. **The physical transform retains dq/q and the exact support payment.** PacketBudget lines 43-148 bound the existing `realOrderTestTransform`, whose integrand is `spectralTest k Y q * K_alpha(q)/q`. The existing test has norm at most one and vanishes outside `[Y/16,16Y]`. Its measure `(255/16)*Y` cancels the reciprocal lower endpoint, yielding exactly `255*kernelBudget(Y/16,alpha)`. Paying the denominator and order factors gives

   `||T_K|| <= G(Y)*(1+1/Y)^|alpha|`,

   `G(Y)=8160*2^theta*16^theta*ell(Y/16)/(1+Y)`.

   The common-order mode integral is the actual transform times the unchanged `completedPacketSum`, so its norm is bounded with that sum still explicit. No coefficient estimate is required by the transform result.

3. **Physical scale and squared weights are preserved.** PacketBudget lines 163-237 derive the square split from `sqrt(X0)>=1` and positive-base real-power identities. With `X=1/Y`, `X0=1+Z/L`, `T=max(V,Z^2/V)`, and

   `R=2/T+8*C^2*Z/(16*pi^2*A*nu*(L+Z)*(V+Z)^2)`,

   the result is `||T_K||^2 <= G(Y)^2*X0^tau*max(1,R^theta)*T^tau`. The consumed geometry theorem retains `Y=4*pi*sqrt(A*V*U)/(C*sqrt(Z))`; the full `16*pi^2` is present. PhysicalNormalization lines 37-66 insert that literal scale and `L=U/nu`, discharging the scale identities. The condition `lambda>=975/4096` remains explicit; conversion to `tau<=7/32` is arithmetic, not an actual Kim-Sarnak instance.

4. **The opposite-sign normalization is exact but separately scoped.** PhysicalNormalization lines 71-92 define `(4/pi)*cos(pi*alpha/2)*T_K` and bound its norm by `(4/pi)*G(Y)*(1+1/Y)^|alpha|`. This agrees with the exceptional specialization of Pascadi (3.18). The squared A/J theorem is for bare `T_K`; squaring the separately normalized expression retains an additional `(4/pi)^2`. No automorphic equality or positive-sign J-Bessel estimate is asserted. The fixed-level A range lemma proves a factor-two inclusion when `z>=Z`; it does not instantiate either norm theorem. The primary statements also require A's length at least 1/2 and cusp density 1/z, and J's lengths at least 1/2, common phase, and infinity scaling Id. These conditions stay pending. [Pascadi v3, Theorems A/C/J and (3.18)](https://arxiv.org/html/2404.04239v3)

5. **Finite smoothing keeps the actual energy.** PhysicalNormalization lines 107-167 apply triangle inequality, the already-proved summability of `actualCoeff`, and weighted finite Cauchy with `c_k=||actualCoeff||` and `s_k=||completedPacketSum||`. They obtain

   `||finiteSeparatedIntegral||^2 <= [G(Y)*(1+1/Y)^|alpha|]^2 * actualW(rho,sigma,0) * E`,

   `E=sum_(k in K) ||actualCoeff(rho,sigma,k)||*||completedPacketSum(P,k)||^2`.

   E is an explicit retained quantity, not a smallness assumption and not a substitute for an A/J spectral norm or the original counting norm. The physical packet update leaves the arithmetic completed sum, signed cusp coefficient, rows, n carriers, one interval `Ico(lo,hi)`, and phase `k1/(64V)` unchanged. Its Fourier coefficients and E are correctly evaluated at the inserted physical rho; the code does not falsely assert that E is invariant under a change of rho.

6. **The smoothing constant has the correct order of choice.** Lines 171-198 choose B>0 from the actual normalized-F derivative/Fourier theorem before every packet, physical scale, x, eta, order and finite mode set. From `D>0`, `C>0` and `V<=x^eta*C/D`, they derive `rho=V*D/C<=x^eta`, and use `x>=1`, `eta>=0`, `|sigma|<=1` to pay `actualW<=B*x^(12*eta)`. The one Fourier L1 debit is visible; the remaining Fourier-weighted energy is unchanged in role. No second retained five-coordinate phase charge appears. Paying the explicit logarithmic Y cost and assembling the original selectable subpower threshold remain separate.

The theorem signatures contain no Eq24 estimate, spectral mean, A/J target norm, final polynomial bound, or equivalent internal-target assumption. PacketData's hypotheses are finite carriers, positive scales and the existing normalized-coordinate box; CoprimePacket retains its coprimality and ordinary coefficient data. No new axiom, sorry/admit, unsafe declaration or decision execution was found in the three new sources. Relevant real-power, continuous-map norm, set-integral and finite-Cauchy API signatures were checked by reading available Mathlib sources. This is not an elaboration check, and inherited source-only proofs are not kernel-certified here.

The remaining internal obligations are substantial and stay OPEN: the original nonzero Poisson source to normalized automorphic Kuznetsov dictionary and signed cusp conversion; actual exceptional spectrum and normalized Fourier coefficients with a genuine Kim-Sarnak instance; positive-sign exceptional J-Bessel normalization; actual A/J norm applications with dyadic nonempty carriers, common partial-interval completion and level Cauchy; coprime ABL oldform packet identity/norm and cancellation of `(A*nu)^theta` in the improved term; a bound on the retained coefficient energy; full Fourier/spectral sum passage; the original auxiliary nu source and subpower sum; logarithmic scale payment; and attachment to Eq24, Eq25/H, the two square roots and E2/full medium. Radial KL form identities, scalar Friedrichs moments and the finite Hecke coefficient formula do not discharge these automorphic obligations.

No contradiction was found in the reviewed local mathematics. The precise finding is a useful source-only K-transform and finite smoothing advance, not completion of the exceptional spectral branch. The original c=49044063/25000000 and K=8452171/1250000, the moving-residue conditions and the manuscript's c0/sigma/kappa quantifiers are unchanged. Every shell explicitly selected the repository. Only this review pair was written; no Lean/compiler/build/CI, numerical certificate or finite-decision replay, producer execution, Git operation, subagent or quota call was used.
