# P5.6 h34 — external-input boundary: root presieve obstruction

Pinned manuscript: `UyNewNas/chen-imbalanced-semiprimes@ba6ec11d800eccc54406490631895e174de85766`; `paper/source/manuscript-body.tex` blob `d529bea2ecfcc74d64fc1664ac770a3becaa7c79`.
Previous h34 branch HEAD `483d78d1fc50ca7eaabef4b6c1e162dc6b67c39d`.
Source commit `53e3f430a8fdd373c08e5599681409e2cefcfa82` / blob `f4f927abc73b61964c8c0b84b2d3dbfb8ab73710`.

**New external analytic inputs: NONE.** No PNT, Mertens, BV, analytic-density lemma, numerical table or replacement axiom implemented.

Actually used generic library facts: `Finset.mem_filter`, finite-set extensionality, transitivity of `≤` and `<`, `not_lt_of_ge`, `Finset.mem_sdiff`. These are elementary Lean/Mathlib components.

Existing **manuscript-internal** sources used, without reclassification as external:

- `Part5OriginalH430TaggedArithmeticReceivers.originalBand` and `ChenQuotientPrimeSource.chenSinglePrimeSelector`: membership of p in either band gives the literal lower bound `(N : ℝ)^a ≤ p`; used in `original_band_lower_power`.
- `Part5OriginalH430RootDiagonalElimination.raw_root_in_original_band`: traces each raw U3/U4 (band,p,q) receipt to its actual original prime selector; used in `raw_root_lower_power`.
- `Part5OriginalH430ReceiverRootGateAccounting.rootLicensed` and `gateBlocked`: retain their physical strict cutoff and Rosser test; used in `raw_root_not_licensed` and `all_raw_gate_blocked`.
- `Part5OriginalH430TaggedSourceRejections.frozenOnly`, `rejectedFrozen`, `rejected_original_card_split`: retain both real rejection sources, overlap tags and q occurrences; used in cutoff-specific cardinal result.
- Existing `mem_roughPrimeUniverse_iff_of_cutoff_le_cap`: initial carrier membership includes `p<z0`, provided `z0≤cap`; used only in `raw_root_not_initial_carrier`.

Unresolved manuscript-internal check: whether the fixed consumer presieve `z0=N^ω` actually satisfies `z0≤N^a` or `z0>N^a` at each history stage; no value of ω was invented or silently imported. The root cut/owner repair, PP/same-rho, selected-count closure and 430+11 refinement remain internal. Source-only upstream interfaces are also uncompiled.

SOURCE_ONLY / UNCOMPILED / UNEVALUATED. Numerical430 is UNEVALUATED; kernel replay, transitive axiom audit and independent review NOT RUN.
