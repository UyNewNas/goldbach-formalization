# P5.6/h34 — external-input audit and pin (root diagonal elimination)

- Fixed manuscript: `UyNewNas/chen-imbalanced-semiprimes@ba6ec11d800eccc54406490631895e174de85766`; file `paper/source/manuscript-body.tex`, blob `d529bea2ecfcc74d64fc1664ac770a3becaa7c79`.
- Inherited h34 branch HEAD before source: `2b1beb007342cb63e8ae9d0ee7da077c6ac65d4a`.
- Source commit: `854402e39b87ae307ffd01f4f029734aa356d549`; blob `eb5cc9da305095cf89260c5029be22d7edab8d73`.
- **New external analytic inputs: NONE.** No PNT/Mertens/BV theorem, new distribution licence, new axiom or alternative external table is supplied.

## Actually used library interfaces

Mathlib/Lean `Finset.mem_sigma`, `Finset.mem_sdiff`, `Finset.mem_filter`, finite-set extensionality, natural gcd and divisor arithmetic (`Nat.dvd_gcd`, `Nat.le_of_dvd`), elementary prime `one_lt`, Boolean and list constructors. These are routine library invocations, not a new external number-theory assumption.

## Existing manuscript-internal declarations actually consumed

- `Part5OriginalH430TaggedArithmeticReceivers.original_band_prime` and `originalBand`: the original `chenSinglePrimeSelector` in each U3/U4 band yields `p.Prime ∧ p.Coprime N`. Used in `raw_root_prime_coprime`.
- `Part5OriginalH430TaggedSourceRejections.rawTagged`, `rawPairs`, `frozen_tagged_subset_raw`, `rejectedFrozen`: literal original arithmetic carrier and its two inclusion paths. Used in `raw_root_in_original_band` and both cutoff-specific nondivisibility conclusions.
- `Part5OriginalH430ReceiverRootGateAccounting.rootLicensed`, `gateBlocked`: prior root-gate definitions rewritten *only on the real raw source*; used in `root_licensed_iff_cutoff_and_rosser` and three exact gate-blocked lemmas.
- `Part5OriginalH430ReceiverRootFrontier.raw_receiver_root_mem`, `receiverRootState`: existing conditional genuine rank-one history. Used in `raw_root_frontier_of_cutoff_and_rosser` with its p∤N argument now derived.

These upstream source-only declarations have not been staged, compiled or kernel-audited by this packet. Their exact preceding branch contents, not an upgraded dependency, are the intended imports.

## Still manuscript-internal, not outsourced

Root cutoff/cap/singleton-Rosser compatibility, full/selected/inherited filters, actual first-excluded owner, original root count weights and occurrence-fibre payments, three remaining eight-lane categories, request Buchstab/retention and full closed-cell induction, base/seed/floor/fixed/switched, PP/same-rho, integral–Theta–count, native-history mass, and the common 430+11 refinement.

SOURCE_ONLY / UNCOMPILED / UNEVALUATED. No CI, external proof, kernel replay, transitive axiom audit or finite table evaluation.
