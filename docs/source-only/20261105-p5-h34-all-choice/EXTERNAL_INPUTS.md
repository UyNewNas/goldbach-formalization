# P5.6/h34 — external-input boundary (record only)

Scope: continuation of b9694b3, manuscript-local proof packet dated
2026-11-05. No new external theorem was introduced or implemented.

## Transitive reused inputs (unchanged)

- Locked Mathlib: Fin, Finset.sum_filter, sum_add_distrib, sum_comm,
  sum_le_sum, sum_nonneg, List/Option constructors, linear real arithmetic
  and ring normalization. These are only used, not reimplemented.
- Earlier manuscript-local local suppliers:
  * `uniform_level_bank_supply` in the 0a3fa5a requested-bank packet:
    a selected bank request row has coefficientwise absolute error
    epsilon Theta, nonnegative coefficients and mass <= 12 Theta.
  * `uniform_level_buchstab_supply` in b9694b3: same selected
    Buchstab request, strict prime ceiling and original previous
    generation, with nonnegative mass <= 5 Theta.
  * `selected_bank_candidate_upper` in the pre-7336071 fixed
    request semantics, with the original base/fixed/feedback candidate
    and read-mode-dependent resolve.
  * `retained_level_exact` in b9694b3: exact old specified cell.
  These are original manuscript-internal suppliers, NOT external
  analytic inputs, and all new source is still uncompiled.

- The earlier raw suppliers may transitively require their own pinned
  prime-profile / PNT / Mertens and fixed sieve-distribution interfaces.
  Their proofs and versions are not changed here, nor is their
  transitive trust closure claimed audited. The precise inherited
  source blobs are recorded in preceding packet REGISTRY files.

## Still manuscript-internal (NOT outsourced)

Complete original U3/U4 selected-count source matching, outer root
weights, scalar/cell source selection and owner multiplicity, full /
selected / inherited rejection filters, count-side CLOSED-CELL
induction, base/seed/floor/correction payments, actual same-rho PP
consumer, outer integrals and one common nested 430+11 refinement
remain internal work. No target-equivalent new premise, axiom or
external proof implementation replaces them.
