# P5.6 h34 — external inputs and source boundary

Status: SOURCE_ONLY / UNCOMPILED / UNEVALUATED.
Fixed manuscript: UyNewNas/chen-imbalanced-semiprimes@ba6ec11d800eccc54406490631895e174de85766,
paper/source/manuscript-body.tex, blob d529bea2ecfcc74d64fc1664ac770a3becaa7c79.

## External proofs

No new number-theoretic input, axiom or external proof is added. The
existing pinned Mathlib finite-set lemmas \`Finset.card_disjSum\`,
\`Finset.card_sigma\`, \`Finset.sum_disjSum\`, \`Finset.sum_sigma\`,
\`Finset.card_union_of_disjoint\`, \`Finset.sum_union\` and elementary
Nat-to-Real casts are invoked from the current project's unchanged
dependency lockfile. Their full transitive dependencies have not been
audited in this packet. No fresh PNT, Mertens, BV or Buchstab proof is attempted.

## Actual manuscript-local interfaces consumed (NOT externalized)

- \`Part5OriginalH430PhysicalRoots.rootQ\` at each \`(N,precision,tag,tau,p)\`,
  rather than one scalar Q shared across the two bands.
- \`Part5OriginalH430RequestedHistory.rootHistory_sameQ\`, consuming the
  original request-history occurrence and its unchanged total Q; used
  in \`physical_Q_U3_history\` and \`physical_Q_U4_history\`.
- \`Part5OriginalH430OriginalSelectedRootFibres.selected_root_licensed_iff\`,
  which itself uses the actual \`originalTagged\` source and the proved
  original root prime/coprime fact; used in
  \`original_physical_licence_iff\` and \`physical_root_blocked_split\`.
- \`Part5OriginalH430TaggedArithmeticReceivers.original_U34_eq_tagged_card\`,
  used in \`actual_physical_selected_count_three_terms\`.
- \`Part5OriginalH430OriginalRootCutoffObstruction.raw_root_not_licensed\`,
  used only in \`physical_selected_all_cutoff_if_small\` under the
  explicit assumption \`z0 <= N^a\`.

The existing analytic inputs and original c/K, root norm 7/2,
row norm 12, alpha, exact same-root Q, closed-node requests and 430+11
reserve order are not changed.

## Still internal, NOT assumed or outsourced

Correct stage and actual numerical/power identity for z0, root-dependent
lower/upper parity and alpha, original full/selected/inherited filtering,
actual owner and q multiplicity, signed historical payment and all non-event
rejection families, CLOSED-CELL arithmetic induction, base/switched/seed/
floor, feedback-to-integral/Theta/count, manuscript-local PP/same-rho,
native-history and common 430+11 refinement.

This packet proves no unconditional count-to-history theorem. Finite
certificates remain UNEVALUATED, not accepted by static checks.
