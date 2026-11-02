Independent source review of K task `exceptional_j`, by `/root/j_review_exceptional`, 2026-11-02.

**Verdict: SOURCE_REVIEW_PASS_FOR_POSITIVE_J_SMALL_PROFILE_AND_PHYSICAL_RECONSTRUCTION_ONLY.** The frozen source proves a substantive cancellation estimate for the actual normalized positive J kernel, connects it to the original smooth packet through an exact all-mode Fourier HasSum, and supplies quantitative transform/AJ-weight/smoothing bounds only on the explicit domain `Y<=1/16`. The full positive-sign transform, exceptional Eq24 and P3.5.uniform_spectral remain **OPEN**. `compiled=false`, `kernel_verified=false`, `formal_credit=0`, `task_complete=false`.

This reviewer wrote the earlier independent J exceptional review, but did not author the J or K proof candidates. The present verdict comes from reading the K proof bodies and their actual suppliers; the predecessor's pass is not treated as kernel verification or as automatic acceptance of K.

The reviewed freeze is exact:

| Artifact | Raw SHA256 |
| --- | --- |
| REGISTRY.json | 3de01f73bced71ca00f6bdc192357771dd42e167fd8e811893221b78adda8148 |
| REPORT.md | b9a425ecf07122810ca6722c683e2b3f357859327a1c73c32f9fc7ffefa871dc |
| Part3ActualExceptionalJSmallKernel.lean | 5241315ed4d8f685bfd2debaabdf7a578f45f7288d45c2a4ddc0e170fe8d9763 |
| Part3ActualExceptionalJPacketAdapter.lean | 9e2fe13c39c477a8798608c150c530b8e6711c4f0bc42c04070405360c5e56e5 |
| Part3ActualExceptionalJSmallPacketBudget.lean | dfafb95066e1ae19eef26fba5495c8342f05d0b1b18b3c210f3bc24672ca4bf1 |

All 50 registered project/source/reference/report/Mathlib path-and-hash entries match current raw bytes. The five entries in FREEZE also match. All three new import lists and their 47 public declaration entries agree with source text; their production installation targets remain absent as recorded. The J draft locations and hashes are retained accurately. This pin audit does not authenticate every recursive import or establish a whole Mathlib package revision.

The K README and exact TASKS row were read. The original manuscript at 116-255, especially its parameter range and spectral boundary, the medium completion at 349-380 and 454-484, and the frozen J source/report/registry were compared with the delivery. The fuller original completion, classical correspondence and ABL audit had also been read in the preceding J review; all their pins remain unchanged. J supplies a K-transform and finite smoothing step, not an exceptional spectral return. Its scalar threshold algebra is legitimately reused here without treating either A/J norm as already proved.

The concrete findings are as follows.

1. **The special function is the existing actual general J.** `generalJ` is the production principal-power alternating Gamma-series function, with its proved symmetric Poisson representation. SmallKernel lines 69-217 use the actual reciprocal Gamma factor and native derivative on the fixed compact interval `[-7/32,7/32]`. That interval lies strictly inside `Re(nu)>-1/4`. The order `-3/8` Poisson weight is integrable; it dominates the ordinary integral, while the existing logarithmic envelope dominates its order derivative. These are genuine fixed masses and compactness bounds, not requested estimate fields.

2. **The derivative estimate preserves the current order radius.** The principal-power estimate is `(q/2)^nu <= 2^(7/32)*q^(-a)` whenever `|nu|<=a<=7/32` and `0<q<=1`. Combining the three actual differentiated Poisson/Gamma terms gives one D>0, chosen before a, nu and q, such that

   `||d_order J_nu(q)|| <= D*(1+abs(log q))*q^(-a)`.

   The proof does not replace a by the worst-case cap in the singular q power. Thus the subsequent mean-value theorem can use the shrinking segment `[-alpha,alpha]` with the exact power `q^(-alpha)`.

3. **Cancellation is uniform through alpha=0.** SmallKernel lines 291-349 apply the real mean-value norm theorem to the actual complex-valued J function on that segment. The numerator is at most `2*alpha*D*(1+abs(log q))*q^(-alpha)`. Jordan's inequality supplies `sin(pi*alpha/2)>=alpha`; cancellation occurs before division. At alpha=0 the kernel is explicitly `2*actualJOrderDerivative(0,q)`, paid by the same constant using `2<=pi`. The existing analytic dslope quotient and its zero limit justify this value. It is neither totalized zero division nor a hidden `1/alpha` bound. `smallKernelConstant` is chosen from this proved existence statement.

4. **The positive normalization has the right sign and factors.** The kernel is

   `H_alpha(q)=pi*(J_alpha(q)-J_(-alpha)(q))/(2*sin(pi*alpha/2))` for alpha>0,

   `H_0(q)=2*d_order J_0(q)`.

   Lines 243-287 prove equality to `-(pi/2)*criticalJRealKernel(q,i*alpha/2)` and the literal positive formula in Pascadi (3.18), retaining pi, 2 and i. The paper chooses the exceptional representative with `i*kappa>0`; reversal of the imaginary representative changes both numerator and sinh signs. The existing `criticalJQuotient_even`/`criticalJRealKernel_even` confirms invariance. Thus no sign defect is concealed by the chosen representative. This is a special-function normalization check, not an automorphic Kuznetsov identity. The saved primary extraction at (3.17)-(3.18), Lemma D and Theorems A/C/J was read and hashed. [Pascadi v3](https://arxiv.org/html/2404.04239v3)

5. **The Fourier HasSum is exact and retains the original packet.** PacketAdapter lines 33-216 change only `PacketData.kernel` to a continuous extension of `H_alpha(q)/q`, equal to the literal expression on the physical region. Positive-q continuity at alpha=0 comes from the existing actual mixed derivative theorem. Physical equality, integrability, mode equality and factorization are proved before the existing integral reconstruction is applied. The resulting HasSum has terms

   `actualCoeff(rho,sigma,k)*positiveSignTestTransform(P,k,alpha)*completedPacketSum(P,k)`

   and sum `integral positivePhysical(P,alpha)`. It holds for every positive Y and `0<=alpha<=7/32`, independently of the small-Y estimate. It preserves normalizedF, all row/n carriers, signed cusp coefficient, modePacket, the one `Ico(lo,hi)` completed interval and physical phase `k1/(64V)`. This is a Fourier reconstruction of the smooth packet; it is not a spectral/automorphic expansion.

6. **Every quantitative bound keeps the small-scale gate.** SmallPacketBudget lines 62-177 use `Y<=1/16` to place the entire existing support `[Y/16,16Y]` inside `(0,1]`. The proved test norm and exact measure `(255/16)*Y` give

   `||T_J|| <= 255*B*(1+abs(log(Y/16)))*(Y/16)^(-alpha)`

   `          <= G_J(Y)*(1+1/Y)^alpha`,

   `G_J(Y)=510*B*16^(7/32)*(1+abs(log(Y/16)))/(1+Y)`.

   The factor255 is the support-length/reciprocal-q payment; `16^(7/32)` pays the endpoint conversion without changing alpha. The extra factor2 uses `1+Y<=2` on this restricted domain. It does not prove decay by oscillation for large Y. The gate is present in the mode, squared-weight, physical and finite-smoothing statements, including the final uniform theorem.

7. **The physical A/J geometry is unchanged and still conditional.** Lines 182-261 insert J's literal physical packet with `Y=4*pi*sqrt(A*V*U)/(C*sqrt(Z))`, `rho=V*D/C`, and `L=U/nu`. The scale gate is proved equivalent to `4096*pi^2*A*V*U<=C^2*Z`; it is not asserted for all original packets. The square split yields

   `||T_J||^2 <= G_J(Y)^2*(1+Z/L)^tau*max(1,ratioBound^theta)*max(V,Z^2/V)^tau`.

   The ratio retains its `16*pi^2*A*nu*(L+Z)*(V+Z)^2` denominator. The explicit `lambda>=975/4096` condition is only converted arithmetically to `tau<=7/32`. Unlike J's bare K transform, this T_J already includes the positive normalization. No A/J norm theorem, actual eigenvalue instance, or ABL cancellation is inferred from the scalar comparison.

8. **Finite smoothing retains exactly the predecessor's coefficient energy.** Lines 270-349 reuse `finiteCompletedEnergy`, with no new surrogate:

   `E=sum_(k in K) ||actualCoeff(rho,sigma,k)||*||completedPacketSum(P,k)||^2`.

   Triangle inequality and weighted Cauchy give `||finiteSeparatedPositiveIntegral||^2 <= [G_J(Y)*(1+1/Y)^alpha]^2*actualW(rho,sigma,0)*E`. The derivative/Fourier supplier chooses B0 before every packet, scale, alpha and finite K; the original cutoff `V<=x^eta*C/D` gives `rho<=x^eta`, hence `actualW<=B0*x^(12*eta)`. The physical update retains the arithmetic completed sum and evaluates the Fourier weights at the inserted rho. E remains unestimated. No count norm or spectral target replaces it, no second retained five-coordinate phase charge appears, and the final theorem still requires the physical small-Y gate.

No desired J bound, Eq24, A/J target norm, coefficient-energy bound or ABL removal estimate is a premise of the new proof chain. No sorry/admit, new axiom, unsafe declaration or finite-decision command was found in the three sources. Relevant Jordan, real-power, mean-value, compactness, set-integral and finite-Cauchy signatures were read from available Mathlib sources. These observations are static; neither the new code nor its imported candidates have been elaborated or kernel-certified by this review.

The unresolved original work remains explicit: large-Y oscillatory positive-J transform estimates and the corresponding mode/derivative/Fourier costs; the original nonzero Poisson-to-normalized-Kuznetsov and signed-cusp dictionary; actual exceptional spectral objects and a genuine Kim-Sarnak instance; actual A/J norm application with nonempty dyadic carriers and common partial-interval/phase completion; coprime ABL oldform packet norm and cancellation of `(A*nu)^theta` only in the improved term; an estimate for E, full automorphic spectral passage, level Cauchy, auxiliary-nu and logarithmic subpower payments; and Eq24/Eq25/H/two-square-root/E2/full-medium assembly. The small-Y theorem does not cover the large-Y complement, and the all-mode HasSum does not close that analytic gap.

No contradiction was found in the reviewed local mathematics. The original c=49044063/25000000 and K=8452171/1250000 and original c0/sigma/kappa ranges are unchanged. This is partial-domain progress, with the full requested task OPEN. Only `K/reviews/exceptional.json` and `K/reviews/exceptional.md` were written. Every shell explicitly selected the repository. No compiler, Lean/lake/build, CI, certificate/finite-decision replay, producer execution, Git operation, subagent or quota call was used; J remains frozen.
