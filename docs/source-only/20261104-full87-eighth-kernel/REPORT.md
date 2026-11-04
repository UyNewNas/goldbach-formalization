# P1.4 — actual eighth-kernel integrability and quantitative endpoint transport

Date: 2026-11-04. Parent: `006cb19d7e0309fb8bc9887a35fc03b6c3ef9802`.

**SOURCE-ONLY CANDIDATES. Uncompiled; no kernel replay, transitive-axiom acceptance or independent review. The WHOLE P1.4 yellow node remains OPEN.**

## 1. The exact manuscript quantity, not an arbitrary integrable weight

The inspected manuscript passage is `UyNewNas/chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b`, `paper/source/manuscript-body.tex:434-451`, blob `d529bea2ecfcc74d64fc1664ac770a3becaa7c79`. It displays eq:current-eighth-saving with factor FOUR, no Chen quarter and no ordering factorial.

Write S=sum(t_i), J=prod(t_i), R=comparison(c,t), M=newCap(c,t), and a=53/13824. The new `kernel` is exactly

    K_c(t) = 4*(M-R)/((R-S)*(M-S)*J).

The original Source predicates, comparison caps and new caps are reused without modification. From the literal source's last-coordinate cutoff and strict ordering, every t_i>a and J>=a^8. The existing original-ideal residual and comparison inequalities give

    a < t_8 < R-S < M-S < 3*t_8.

Consequently the candidate `kernel_bounds` proves

    0 <= K_c(t) <= B := 4/a^9

on the ENTIRE original open Source(c), not just a new compact subset. Measurability follows from the existing continuous affine cap definitions; the source has finite volume. `integrableOn_kernel` therefore supplies actual kernel integrability rather than accepting the generic weight-integrability premise used by preceding omission theorems.

This is particular to these adopted eighth sources and their positive cutoff. It does not assert that all earlier-rank or noncompact kernels are bounded.

## 2. A quantitative rounding debit with the original normalization

The existing `finiteCap n c t` and its one-step-biased floor are unchanged. Let h_n=1/(n+1) and L=finiteCap(n,c,t). On the existing trim(c,width(r)), if 4*h_n<width(r), the inherited cap-licence theorem gives R<L and

    0 <= M-L < 2*h_n.

For the same R,S,J the exact residual identity yields

    K(R,M)-K(R,L) = 4*(M-L)/((L-S)*(M-S)*J).

All three denominator factors have lower bounds supplied above. Thus the candidate `rounded_kernel_loss` proves

    0 <= K(R,M)-K(R,L) <= C*h_n,  C := 8/a^10.

No second rounding, new endpoint normalization or signed-coefficient monotonicity is used. The constants are deliberately conservative: B is about 2.235016e22 and C about 1.165919e25. They establish existence of a finite precision before N; they are NOT an efficient computed mesh threshold, a sharp numerical saving estimate, or a materialized certificate table.

## 3. Actual integrals and one common analytic budget

`retainedKernel r n c` is the analytical comparison function equal to K(R,L) on the original trim and zero off it. It does NOT modify or filter the policy's arithmetic occurrence list. Candidate proofs establish its measurability, integrability and 0<=retainedKernel<=kernel on Source(c).

Define V=sum_c integral_Source(c) 1. The source sum is finite and each source has finite volume. `totalKernelLoss_eq` identifies the actual sum of integral differences. `totalKernelLoss_budget` gives

    0 <= sum_c integral_Source(c) (K_c-retainedKernel_c)
      <= totalOmitted(r,K) + C*h_n*V.

`totalOmitted_kernel_le_volume` additionally proves

    totalOmitted(r,K) <= B * totalOmitted(r,1).

This is important for compatibility: the trim already returned by the actual shared-history supplier can be reused. No independent trim index is silently substituted into its source membership theorem.

`exists_common_eighth_kernel_transport` supplies one cofinal trim index and, for each retained trim, one cofinal n threshold making the sum of actual kernel integral losses smaller than any epsilon>0. There is no assumed integrability or target saving endpoint in this terminal.

The existing licensed-box L1 theorem is also instantiated with this SAME proved-integrable kernel. It now bounds the actual eighth-kernel weight on the joint rejected-box union, rather than just its Euclidean volume. The proof does not instantiate unrelated sixth/other-rank kernels.

## 4. The parent really belongs to the NEW filtered policy

`actualParent` is merely the own-sixth projection of the existing `P4AOriginalFull87LicensedSixthPolicy.level6Exponent`. It is not a new cap, producer, policy or rho.

On the original87 realized-history slice, the original activation theorem identifies this level with the existing `licensedCap`. H7 at the original third ancestor and the already proved cap chain give

    t_8 < actualParent-S,
    actualParent <= R < L.

The first inequality survives the real fifth fallback; safe8 is NOT an input. The candidate `actual_eighth_kernel_transport` then gives

    K(R,M) <= K(actualParent,L) + C*h_n,
    t_8 < actualParent-S <= R-S < L-S < 3*t_8.

Only the residual expression is monotone in its positive comparison-parent denominator. This is NOT a theorem that arbitrary signed continuations, physical sums, or archived gains are monotone in a cap. In particular the new and old rank-eight frontiers are not identified.

## 5. Same source membership, same quantifier order

Terminal import:

    ImbalancedChen.P4AOriginalFull87EighthKernelIntegration

Terminal theorem:

    exists_shared_licensed_eighth_kernel_schedule

For epsilon>0 and the preceding sixth-volume tolerance, the proof invokes the existing licensed-box schedule with source-volume tolerance epsilon/(4B). It retains THAT returned source trim and all original coarse choices. For fixed e,q,omega it increases the cofinal n threshold to satisfy the eighth cap licence and C*h_n*V<epsilon/4. For fixed n it increases the cofinal joint box threshold to make the ACTUAL kernel-weighted rejected-box mass smaller than epsilon/2. All choices precede N and prime tuples.

The output preserves ArchiveLicenses, SixthLicenses, FilteredSourceSupply (hence the SAME new-tree occurrence members), CompiledLicensedSupply, SavedSourceSupply and LowerWinnerSupply. It adds ResidualSupply as a conclusion, plus

    totalKernelLoss(r,n) + licensedBoxOmitted(n,e,q,omega,m,K) < epsilon.

The sixth tolerance is still its preceding volume tolerance. It has NOT been reinterpreted as a paid sixth signed-gain error. No state is removed by declaring its real source/box mass small.

## Remaining manuscript-internal obligations

1. Identify the actual NEW eighth signed occurrence/frontier source and its arithmetic mean with the residual integrals on the SAME producer and domain; handle its full modulus/beta normalization, multiplicities and genuine boundary/repeat exceptions. The new real-kernel inequality does not supply this bridge.
2. Quantify the sixth filtered-action loss and the other raw/finite/filtered changes, then prove full changed/tagged arithmetic coverage and the separate compiler/density reserve payments. Neither u_c nor u_d is paid here, nor is a final same-rho density conclusion derived.
3. Authenticate the entire intended saved array, original source/integral coverage and numerical gain endpoints beyond the earlier original87 overlap. No original NPY/BIN producer was rerun.
4. Stage the exact effective dependency and fixture closure, elaborate the pinned Lean sources, evaluate inherited finite certificates, replay the kernel, audit transitive axioms and obtain independent review.

External analytic inputs remain documentation-only in INPUT_BOUNDARY.md. The proof of actual-source integrability and residual transport is manuscript-internal and is not moved into the external-input ledger. No new axiom, placeholder proof, toolchain upgrade or external analytic implementation is introduced.

## Checks actually performed

Three new Lean modules: 591 lines, 48 named declarations. The audit checks nested comments/strings, prohibited escape tokens, delimiters, local declaration duplication, imports, new-module acyclicity and content hashes. These are lexical checks, NOT a Lean parser or type checker.

The independent Fraction model passes 1,061 cases: 189 residual identity/bound/parent comparisons; 567 nonzero endpoint-loss comparisons; 255 exact floor boundaries and unrestricted floor inputs; 40 synthetic eight-coordinate cutoff examples; 10 finite-measure accounting examples. The synthetic tuples are NOT asserted to satisfy any literal Source or archive row. The audit does not evaluate Lean proofs, Lebesgue integration, arithmetic means, or original data. Reproducibility is checked by rerunning the audit and comparing its JSON bytes.

Same-author review checked the normalization four, signs and denominator positivity, conservative parent direction, no second debit, source versus retained-domain accounting, actual versus ideal parent, independence from safe8, and compatibility of the trim/precision/box quantifiers. No independent reviewer participated.

Read through connected GitHub: the exact base branch, the manuscript passage at its fixed pin, the original87 source dictionary's actual cutoff/residual facts, and the pinned mathlib floor-measurability and integrable-domination signatures. Prior finite-cap, trim, parent and integration suppliers were inspected from the mounted handoff archives. This is not reauthentication of the entire latest manuscript, all dependency sources or the numerical archives.

No Lean/Lake executable was found on PATH. No Lean compilation, kernel replay, proof evaluator, transitive-axiom audit, original numerical producer, Codex invocation, user-computer connection or CI dispatch was performed.

Pins unchanged: Lean `leanprover/lean4:v4.33.0-rc1`; mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`; native `subfish-zhou/goldbach-lean@09b97db5764ade1246bfb77206baa1b124760958`. Preserve the inherited source-only replacements and original fourth/fifth/sixth fixtures. This packet is NOT a complete dependency bundle.

Publication: new `chatgpt/p1-full87-eighth-kernel-20261104` branch, `[skip ci]`, no merge, existing-branch move, workflow change or prior proof-file modification.
