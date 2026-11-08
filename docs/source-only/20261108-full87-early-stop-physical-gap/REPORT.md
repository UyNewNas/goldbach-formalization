# P1.4 — retain the missing pre-eighth stopped physical contribution

## Recovery and actual mathematical correction

Recovered the real previous branch HEAD ac1d83cf798923371a581a6dd5efb01bc5eecd07 from \`chatgpt/p1-full87-three-class-leaf-invoices-20261108\`; read the previous full Lean packet, REPORT, REGISTRY, INPUT_BOUNDARY and HANDOFF, the actual raw and licensed frontier/producer modules, the signed root-to-frontier lemma in \`P1Pair12RetainedSignedSource\`, the full physical source, and pinned manuscript §4. The root, docs, source-only, and preceding packet AGENTS.md lookups were not found. The independent continuation branch is \`chatgpt/p1-full87-early-stop-physical-gap-20261108\`. No other branch was changed.

**Found a substantive missing term in the preceding finite accounting:** the previous five physical leaf classes bound only the difference of the *rank-eight frontier continuations* of the complete-sixth raw and licensed-sixth producer. Since the two producer policies can disagree already at rank five/six, they can also differ on signed branches which **exhaust their carrier before reaching rank eight**. Those branches occur in \`stoppedTest 8\` and do not appear in either depth-eight List. Consequently a frontier difference bound by itself is NOT a bound on the difference of full physical signed coefficients.

Using the actual \`physical_test_eq_signedTest\` and the existing proved-source \`signedTest_splice_eq_stopped_add_frontier\` instantiated with \`parent = fresh = R\`, the candidate now proves for ANY even-retaining policy

    physical(R; strict full-q X) =
      stoppedTest(8,R; strict full-q X) +
      sum_{s in actual rank8 frontier(R)} signedTest(R,s; strict full-q X).

In particular, for the two **different actual policies** RAW and LICENSED,

    physical(RAW)-physical(LICENSED)
      = [stopped(RAW)-stopped(LICENSED)]
        + [frontier(RAW)-frontier(LICENSED)].

The second bracket is *exactly* the earlier source-specific five-class ledger. The new FULL physical bound is therefore

    |physical(RAW)-physical(LICENSED)|
      <= |stopped(RAW)-stopped(LICENSED)|
         + rawOutsideHighQInvoice
         + actualProducerThreeClassLeafBill
         + licensedOutsideHighQInvoice.

The middle invoice is already three separate matched/raw-only/licensed-only source leaf classes, so the right side comprises six leaf/stop categories without duplicate payment. The early-stop discrepancy is not set to zero or declared small; it is a **new substantive yellow quantitative obligation**. The previous frontier-only finite theorem remains valid; only its interpretation as a full physical bound is corrected.

No hypothetical coefficient, assumed equality of different frontier Lists, replacement of the original sign-dependent small beta, cap monotonic saving, or new input theorem was used. Every full modulus still uses the original strict integer \`X < a * selected.prod\` test.

## New candidate source and evidence

\`docs/source-only/20261108-full87-early-stop-physical-gap/P4AOriginalFull87EarlyStopPhysicalGap.lean\`: 162 lines, Git blob \`9442b25cf2a0a3cfd76a255c19d4bf6b291c0156\`, source commit \`b070cbbb5ceefa11085af1205e16cbc5ef642fc1\`. New actual proof bodies:
- \`physical_eq_stopped_plus_rank8_frontier\`
- \`actual_full_physical_difference_eq_stops_and_frontiers\`
- \`abs_actual_full_physical_difference_le_stop_and_five_leaf_classes\`

GitHub readback confirmed exact source blob, 162 lines, three \`:= by\` bodies. Forbidden proof-token scan and simple delimiter check passed. 4,000 seeded synthetic integer first-exit recursions with different even-retaining early policies checked the rank-k stopped/frontier conservation; zero failures. In 2,542 cases early stopped sums disagreed, reinforcing that they cannot be silently identified. A one-element carrier at k=8 has no frontier but unequal signed stopped totals for two genuine different policy choices. **These are synthetic structural checks only; not Lean elaboration, not saved87 replay and not a number-theory estimate.**

Validation remains SOURCE_ONLY / UNEVALUATED / UNCOMPILED. No local Lean/Lake, CI, kernel replay, transitive axiom review, independent peer review or saved87 physical replay; no Codex, desktop access, new resources or reserve spending.

## Boundaries, open obligations, next actual mathematical step

The specific new unpaid problem is the SAME signed small beta / full-q high-tail discrepancy on branches exhausted before eighth rank. Derive its first-policy-disagreement source on the earlier retained fifth/sixth frontier, preserving sign and same historical admissibility. The original and new policies coincide only through four, not through eight. Do NOT assume the early-stop discrepancy is zero or bound it by the five depth-eight bills.

Further open: six-source same \`rho_N\`, same \`H_N\` quantitative payment, legal fixed-before-N integer \`X\`, raw/finite/filtered loss, genuine 87 affine witness/dynamic parent/common histories and signed numerical gain, permitted Gevrey / PP primitive discrepancy and centre/modulus/endpoint costs, ordinary residual integral, rank9, changed/tagged, independent compiler/density reserves and exact Lean/kernel validation.

External manuscript §4 current-PP is REGISTERED_NOT_PROVED at \`UyNewNas/chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b\`, \`paper/source/manuscript-body.tex\` blob \`d529bea2ecfcc74d64fc1664ac770a3becaa7c79\`. Fixed Lean \`leanprover/lean4:v4.33.0-rc1\`, mathlib \`e4c91783ca8e6a7c693ae624ade32fd22d4e43c1\`, native \`subfish-zhou/goldbach-lean@09b97db5764ade1246bfb77206baa1b124760958\`; fixed \`c=49044063/25000000\`, \`K=8452171/1250000\`.

P1.4 remains YELLOW. This packet is a **correction of the physical quantity being bounded**, not an asymptotic saving claim.
