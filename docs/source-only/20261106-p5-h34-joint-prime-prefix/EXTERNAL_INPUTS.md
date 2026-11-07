# P5.6 → h34 joint-prime-prefix: external inputs (record only)

Scope: manuscript-internal proof consumers only. Pinned manuscript `UyNewNas/chen-imbalanced-semiprimes@ba6ec11d800eccc54406490631895e174de85766`; original Lean dependencies/toolchain unchanged.

No new PNT, Mertens, Bombieri–Vinogradov, prime-pair, same-rho or other external analytic proof was implemented; no custom axiom, target-equivalent count licence or admitted source was added.

## Reused imported Mathlib arithmetic, at the repository's existing fixed dependency

- `Nat.prime_dvd_prime_iff_eq`: for `r.Prime`, `p.Prime`, `r ∣ p ↔ r=p`; actually called in `min_root_and_quotient_first_prime` after separating prime divisors of `p*q`.
- `Nat.Prime.dvd_mul`: a prime divisor of `p*q` divides `p` or `q`; used in the same declaration.
- Elementary `Nat.mul_div_cancel'`, `Finset.mem_sigma` and finite membership rewrites: used by `raw_tagged_product` and `raw_tagged_band` respectively.

## Existing manuscript-local providers, NOT external premises

- `raw_label_divides`, `raw_prime_label_data`, `original_band_prime` from the existing tagged original U3/U4 arithmetic receivers.
- `first_bad_spec`, `first_bad_le_every_prime_divisor`, `bad_implies_not_rough` from the predecessor source-only first-obstruction modules.
- Real original and frozen physical cutoffs, `frozenOnly`, `rejectedFrozen`, and `frozen_tagged_subset_raw` have their existing definitions, not replacement licenses.

## Still internal / NOT outsourced

Actual full/selected/inherited historical owner matching, retained-prefix cap tests, odd/even first-exit signs, signed rejection-mass payments, all-action CLOSED-CELL induction, base/seed/floor, PP/same-rho manuscript consumers, native-history and shared 430+11 causal refinement remain open. All external and inherited finite analytical proof dependencies retain their previous verification statuses; no new audit was run.
