# P5.6 h34 — external-input boundary and concrete calls

Pinned manuscript: `UyNewNas/chen-imbalanced-semiprimes@ba6ec11d800eccc54406490631895e174de85766` (`paper/source/manuscript-body.tex`, blob `d529bea2ecfcc74d64fc1664ac770a3becaa7c79`).
Pinned toolchain: `leanprover/lean4:v4.33.0-rc1`; Mathlib4 revision `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1` (unchanged `lake-manifest.json`).

Existing Mathlib/Lean inputs invoked, not re-proved:
- `Nat.find_min` and `Nat.find_spec`: least natural witness and its specification. Called in `first_bad_le_every_prime_divisor` and through previously defined `first_bad_spec`.
- `Nat.mul_div_cancel'`: exact multiplication/division recovery under `p ∣ N-P`; called in `first_bad_divides_difference` and `raw_label_divides`.
- Ordinary `Nat`/real casts and order, `Finset.mem_sdiff`, propositional rewriting and associativity/commutativity; used in the tagged source branches.

The prior source-only manuscript-local definitions `BadPrime`, `firstBadPrime`, `ChenPrimeRough`, `frozenPrimeCutoff`, `frozenOnly`, `rejectedFrozen`, `rawTagged`, `tagged_raw_quotient`, `raw_prime_fibre_iff`, `raw_prime_label_data` and the P-labelled obstruction lemmas are reused *without* treating their proof bodies as certified or external.

No new PNT/Mertens/BV, PP, or same-rho input is introduced. Original full/selected/inherited historical owner, source-to-feedback inequality, signed rejection payments, native-history and common 430+11 refinement remain manuscript-internal OPEN obligations, not new hypotheses or external results. No numerical guard evaluated.
