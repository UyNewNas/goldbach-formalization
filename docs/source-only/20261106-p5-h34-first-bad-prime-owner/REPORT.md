# P5.6 → h34 — first prime-factor obstruction for original quotient receivers

Date: 2026-11-06 UTC. Branch: `chatgpt/p5-h34-request-admission-20261105`.
Actual predecessor: `5f0477e71c63089096db55c89e28e589bb5bac48`; source commit: `18e0f63e64f3d010d0efaaa9f59e6ae9d30c8ef0`.
Fixed manuscript: `UyNewNas/chen-imbalanced-semiprimes@ba6ec11d800eccc54406490631895e174de85766`, body blob `d529bea2ecfcc74d64fc1664ac770a3becaa7c79`.

**PARTIAL_SOURCE_INCREMENT — SOURCE_ONLY / UNCOMPILED / no formal credit.**

## New manuscript-internal source

`Part5OriginalH430TaggedFirstBadPrimeOwner.lean` (193 lines, 12 candidate theorems, 4 definitions; source Git blob `f0b0d5190832be1296b42a6f7e5321e5bbac48d1`) imports `Part5OriginalH430TaggedAdditivePrimeLabels`. It continues the previously established literal `rawTagged`, `frozenOnly`, `rejectedFrozen`, original additive prime `P=N-p*q`, and separate U3/U4 tags.

* `bad_exists_of_not_rough`, `first_bad_spec`: a failed original `ChenPrimeRough cut q` has a genuine prime divisor below the *same* cutoff; `Nat.find` chooses a deterministic smallest failing divisor. No claim that the quotient `q` is prime.
* `frozen_only_fibre_first_bad` and `frozen_only_tagged_first_bad`: for `frozenOnly`, the original first failing divisor lies at or above the actual frozen root cutoff but strictly below original `N^a`.
* `rejected_frozen_fibre_first_bad` and `rejected_frozen_tagged_first_bad`: for `rejectedFrozen`, the first failing prime lies *below* the frozen cutoff `(rootQ/p)^(1/argument)`; these are distinct lanes.
* `rejected_frozen_P_and_obstruction`, `frozen_only_P_and_obstruction`: retain the literal additive-prime label `P` and original quotient identity together with the small-prime witness.
* `rejected_frozen_owner_le_target`, `rejectedOwnerIndex`, `rejectedOwnerFibre`, `rejected_mem_own_fibre`, `rejected_fibre_owner_unique`: the selected first obstruction divides a positive quotient `q≤N`, giving a bounded canonical owner in `Fin (N+1)`; finite owner fibres cannot double-charge one tagged receiver.

This is **an arithmetic first-failure prime-factor owner**, not yet the original manuscript's full/selected/inherited causal-history owner. The exact first-prime owner does **not** pay frozen-only or still-rejected signed mass, establish a link to the full causal first-exit tree, or prove any count-to-feedback inequality. In particular it does not replace the root norm 7/2 by number of q's or interpret one generated root mark as a receiver count. Full/selected/inherited filtering and occurrence multiplicity matching remain open.

## Verification boundary

The new GitHub source commit and blob were read back. Source-only text scan found no `sorry`, `admit`, `axiom`, `unsafe`, `native_decide` or `run_tac` token; nested block-comment delimiters balanced. This is *not* Lean parsing, elaboration, compilation, kernel replay or a transitive axiom audit. No heavy compilation or CI dispatch; numerical430 and finite guards are UNEVALUATED. P1.4/P3.6, production sources, dependency versions, c/K, root norm 7/2, row norm 12, alpha, same-Q rules, 430+11 budget and manuscript pin were unchanged.

## Exact remaining obligations

1. Verify against the literal pinned manuscript source which (tag,p,P,q,first-bad-prime) is a full/selected/inherited historical owner, with an occurrence-preserving map and the correct positive/negative sign. The new prime factor obstruction is not by itself such a theorem.
2. Pay `frozenOnly` and `rejectedFrozen` arithmetic rejection masses through the genuine history/first-exit comparison, without merging the two lanes.
3. Complete all-action closed-cell arithmetic induction, true original root weights and owner normalization, original base/fixed/switched/seed/floor payments.
4. Complete manuscript-local PP/same-rho and feedback-to-integral/Theta/count matching, native-history proper/equality/inherited masses and the single common causal 430+11 refinement.
5. Install in the pinned toolchain, elaborate/compile, kernel-replay and audit transitive axioms; independently evaluate finite guards when allowed.

**Next explicit action:** identify the actual pinned full/selected/inherited history filter and its first-excluded-prefix record for a tagged original (p,P,q); check whether the newly assigned first bad prime can be mapped to that record while preserving sign and multiplicity. Do not treat this local certificate as a global owner identity.

**Complete manuscript-internal h34 proof remains OPEN.**
