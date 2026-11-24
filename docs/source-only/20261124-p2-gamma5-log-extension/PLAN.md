# Finite marked Γ5 logarithmic extension implementation plan

**Goal:** prove that the original bad-Γ5 labelled source atoms lie on the
one plateau of an explicit smooth geometric profile, including the empty
rough tail, without assuming a weight equality or a distribution estimate.

**Approved scope:** root's 2026-11-24 task and follow-up explicitly permit
this geometry substep. The new files remain source-only. No cloud task,
Lean compilation, active-source edit, or driver change is authorized here.

**Architecture:** use the existing `smoothGateUpperStep` on affine margins
in physical logarithms. The old prefix logarithm is a variable, not a
frozen integer or an assumed primality mask. The pair and canonical tail
remain individually indexed. Rank is arbitrary; the cutoff is the literal
`(Q/d)^a0`. The full-product gate uses `log N - log product`, so a fixed
width gives support below `exp width * N`, not `N^(1+width)`.

**Files:** create
`ImbalancedChen/P2FiniteMarkedGamma5LogExtension.lean`, its short actual-U4
caller `ImbalancedChen/P2FiniteMarkedGamma5SeedPlateau.lean`, and a provenance
README/manifest in this directory; do not modify prior sources.

- [x] Define the finite Γ5 gate program, strict/closed endpoints, logarithmic
  profile, and its direct evaluation on arbitrary natural-number slots.
- [x] Write proofs of smoothness in log coordinates, scalar bounds, the exact one
  plateau, and the correct complete-product nonzero-support bound.
- [x] Reuse `badLabels`, `pair_data`, `pair_eq`, `mem_roughNumbers`, and the
  canonical prime-factor list to prove actual-source gate passage and
  plateau equality. Retain the original pair order and all tail repetitions.
- [x] Give the exact full-product identity, explicit empty-tail check,
  and a weighted identity indexed by the original marks and arbitrary
  additive-prime/congruence test, without merging equal products.
- [x] Independently review the statement, endpoints, scale, and dependency
  fingerprints. Record source SHA and the absence of compilation credit.

The module does not construct a complete `Licence`/`Family`, claim global
smoothness after zero extension across the physical coordinate planes,
bound a collar or a VM error, or close `switchedPPBalance`. These are
subsequent obligations. The requested validation here is source review;
root will schedule strict Lean validation when the dependency closure is
available. No duplicate tests of accepted Lean work are requested.

Source-review result: both candidate files were independently checked by
`/root/p2_numerical`. The explicit rational-exponent conversion in
`sourcePair_mem` and explicit profile unfolding were corrected before
freezing the first source. The actual U4 caller was then independently
checked against `scale_and_alpha` and `history_integer_roughness`.
The checked boxes record candidate implementation and source review only,
not Lean acceptance. Root owns dependency resolution and compilation.
