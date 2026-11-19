# P1.4 — one signed true-d coefficient for the actual fifth/sixth policy change

State **SOURCE_ONLY / UNEVALUATED / UNCOMPILED**; P1.4 **YELLOW**.

## Exact navigation and frozen sources

- Previous durable HEAD: \`5a214ff0f39da4e6986aa19e5094f87b2061f5ad\` (\`20261120-true-physical-prime-divisor\` packet).
- Independent continuation: \`chatgpt/p1-full87-true-d-policy-delta-20261120-0710\`.
- Candidate code: \`P1Full87TrueDPolicyDelta.lean\` 260 lines, blob \`3766fde014673b19438287a6b32de6c58aa7bb31\`; \`P1Full87TrueDReceiverDelta.lean\` 75 lines, blob \`e5f11c245ca9766670672c39ca27d7e1f5bf5860\`.
- Source commits \`7b210fa4dacddc7000a7c9fa459f83eb8d2b0c17\`, \`82125ccb1b52d1094b8e58f23314739377736679\`, syntax/boundary revision \`c849f35aaae51ec4d8a75512081a625ded55a4a8\`.
- Manuscript pinned at \`UyNewNas/chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b\`, \`paper/source/manuscript-body.tex\`, blob \`d529bea2ecfcc74d64fc1664ac770a3becaa7c79\`. Frozen Lean/mathlib/native at \`v4.33.0-rc1\`/\`e4c91783ca8e6a7c693ae624ade32fd22d4e43c1\`/\`09b97db5764ade1246bfb77206baa1b124760958\`. The constants c and K are unchanged.

## What was actually derived as candidate Lean

Let the **original** old retained policy be \`R_5\` and the rank-six splice be \`R_6=firstExitDepthSplicePolicy 6 R_5 fresh\`, with original finite fifth row maxima. Define their actual true small/rough physical supports \`S_5,S_6\`, and original attached coefficients \`rho_5,rho_6\`. On \`S=S_5 ∪ S_6\` define a **single**, precisely support-zero-extended signed coefficient

\[
 \delta\rho(d)={\bf1}_{d\in S_6}\rho_6(d)-{\bf1}_{d\in S_5}\rho_5(d).
\]

The new proofs express, for every arbitrary arithmetic test G on the **same true small physical modulus d**,

\[
 \sum_{d\in S}\delta\rho(d)G(d)
 =\sum_{d\in S_6}\rho_6(d)G(d)-\sum_{d\in S_5}\rho_5(d)G(d).
\]

The support is squarefree and coprime to N, the delta vanishes outside S, and **\(|\delta\rho(d)|\le 2\)** from the two existing original one-bounds. One cannot infer \(|\delta\rho|\le1\) or eligibility for the manuscript's PP coefficient class without an additional structural argument. A generic pair of legal values +1 and -1 has difference 2; this is a licence warning, NOT a claimed actual policy counterexample.

The second candidate file uses the **previous packet's original receiver Fubini theorem** to connect the change in actual \`physicalDivisorSum\` on the unchanged \`chenPrimeReceiverSource N\` to \(\delta\rho(d)\) times the same AP-minus-centre fibre. For even N it then obtains the exact single-delta invoice

\[
 \sum_{n\in\mathcal R_N}(R_6(n)-R_5(n))
 =M_N\sum_{d\in S}\frac{\delta\rho(d)}{\varphi(d)}
 +\sum_{d\in S}\delta\rho(d)\Delta_N^{prim}(d)
 -\sum_{d\in S}\delta\rho(d)\frac{C_N^{mod}(d)}{\varphi(d)} .
\]

All finite signs and the negative modulus-prime correction remain explicit. This **does not** establish that the difference coefficient is the certified manuscript \(\rho_N\), that \`fresh\` is the complete frozen 87-domain replacement, or that the actual full87 event list has been mapped. No lower receiver is subtracted or paid in this packet.

## Actual checks and tool boundary

- Both sources were fetched back from GitHub: verified blobs \`3766fde...\` (260 lines) and \`e5f11c2...\` (75 lines), no banned axiom/escape tokens in either. Only the two new proof files changed before this report.
- Exact rational diagnostics: 6,000 random old/new **abstract support** pairs with independently signed coefficients bounded by 1; 18,000 identity tests, zero mismatches; 2,775 of the 6,000 instances had a delta coefficient with absolute value above 1. These test the finite linear algebra, not the actual frozen policy or Lean elaboration.
- Local \`lean --version\`, \`lake --version\`, \`elan --version\`: command not found, exit code **127** for all three. \`/sys/fs/cgroup/memory.max\` = 4294967296 (4 GiB). Fixed-pin type checking could not run; **UNEVALUATED, UNCOMPILED**. No kernel replay, transitive axiom check or independent review.
- No CI/Actions dispatched, no Codex, main/master change, force push, merge, toolchain update or resource increase.

## Isolated staging required for a future compile

The second candidate explicitly imports two existing **source-only** modules that do not yet live in the package's \`ImbalancedChen/\` path. In an isolated checkout/worktree at the frozen pins, stage the following three files **without committing them to main**:

\`\`\`sh
cp docs/source-only/20261120-true-physical-prime-divisor/P4AOriginalFull87TruePhysicalPrimeDivisor.lean ImbalancedChen/P4AOriginalFull87TruePhysicalPrimeDivisor.lean
cp docs/source-only/20261120-true-d-policy-delta/P1Full87TrueDPolicyDelta.lean ImbalancedChen/P1Full87TrueDPolicyDelta.lean
cp docs/source-only/20261120-true-d-policy-delta/P1Full87TrueDReceiverDelta.lean ImbalancedChen/P1Full87TrueDReceiverDelta.lean
lake env lean ImbalancedChen/P1Full87TrueDPolicyDelta.lean
lake env lean ImbalancedChen/P1Full87TrueDReceiverDelta.lean
\`\`\`

This is an unexecuted staging recipe, **not** compile evidence. If the imports are absent or a Lean error occurs, record errors instead of claiming acceptance.

## Unproved manuscript obligations (no new axioms)

1. Actual \`fresh\` replacement and every frozen \`sharedRankFour\` / fifth/sixth ordered occurrence, including RAW/LICENSED/BOTH, rank9, inherited paths, repetition and original signs, to a single eligible physical coefficient. The above generic signed delta is not this certification.
2. Verify the coefficient class after taking a difference: the bound currently shown is 2, not 1. Determine whether a permitted scaling with correctly paid constants or a stronger original-tree argument is required; **do not apply eq:current-PP by fiat**.
3. Final physical cutoff/support and frozen same-\(\rho_N\) smooth labelled-prime-product \`W_N\`, exact coprime mean, fixed-parameter quantifiers and signed PP estimate with correct source/version.
4. Signed discrepancy, modulus-prime, lower-half corrections, actual ordinary residual integral, saved87 numerical source, changed/tagged coverage, two independent compiler/density reserves, and \(H_N\) payment.
5. Fixed-pin Lean elaboration and all subsequent kernel/transitive axiom/independent validation.

The useful new local boundary is a single true-d coefficient for a genuine fifth-to-sixth policy *difference*, with its coefficient-class hazard exposed. This does NOT close P1.4.
