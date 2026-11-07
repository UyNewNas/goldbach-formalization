# P5.6 h34: externally supplied inputs — exponent-separation packet

Pinned manuscript: `UyNewNas/chen-imbalanced-semiprimes@ba6ec11d800eccc54406490631895e174de85766`, `paper/source/manuscript-body.tex`, blob `d529bea2ecfcc74d64fc1664ac770a3becaa7c79`.
Source commit `9632e6757131f9d16e34f367e112e783aeb3672d`, module `Part5OriginalH430PresieveExponentSeparation.lean`.

**NEW EXTERNAL NUMBER-THEORY INPUTS: NONE.** No PNT/Mertens/BV, Buchstab analytic theorem, singular-series estimate or replacement count axiom was imported or proven in this packet.

### Actually used generic library facts

- `Real.rpow_le_rpow_of_exponent_le`: for a real base `1≤x` and exponents `omega≤a`, derives `x^omega≤x^a`; used in `presieve_power_le_original_band_start`. For `N≥2`, the `1≤(N:ℝ)` witness is a standard natural-to-real cast.
- `Finset.mem_filter`, `Finset.ext`, `Finset.sum_union`, `Finset.mem_sdiff`, and order logic: used in finite license/own-lane emptiness and signed ledger.
- These are ordinary Mathlib facts, not new external analytic assumptions. Their exact compilation in this pinned environment has **NOT** been tested.

### Existing manuscript-INTERNAL declarations reused

- `Part5OriginalH430OriginalRootCutoffObstruction.raw_root_not_licensed`, `raw_root_not_initial_carrier`, `all_raw_gate_blocked`, `frozen_all_gate_blocked`, `rejected_frozen_all_gate_blocked`, `rejected_original_count_all_blocked`.
- `Part5OriginalH430ReceiverRootGateAccounting.rootLicensed`, `gateBlocked`, `ownCarrierOutside`, `ownPolicyPass`, `ownPolicyFail`.
- `Part5OriginalH430TaggedSourceRejections.frozenOnly`, `rejectedFrozen`, `rejected_original_partition`, `frozen_only_disjoint_rejected`. Original `(p,q,tag)` receiver multiplicities are retained.

### Manuscript-local gap NOT outsourced

The fixed manuscript's lower tree starts at `w=a` and `w=h`, but presieve `z0=N^omega` occurs as a separately stated symbolic projection (manuscript-body.tex lines 695–696 and 712–719). The numerical `omega`, threshold and its binding to the actual history consumer are **not supplied** by this packet. It would be mathematically invalid to silently identify `w=a` with `omega=a`.

The correct downstream full/selected/inherited owner, original U3/U4 signed count payment, all-action induction, same-rho/PP, causal nested 430+11 and fixed integral weights remain internal. No target-equivalent assumption has been added.

SOURCE_ONLY / UNCOMPILED / UNEVALUATED. No kernel replay, transitive axiom audit or numerical430 evaluation.
