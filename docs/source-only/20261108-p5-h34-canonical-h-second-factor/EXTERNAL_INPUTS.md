# P5.6 → h34 — external inputs boundary (this packet)

Pinned manuscript: `UyNewNas/chen-imbalanced-semiprimes@ba6ec11d800eccc54406490631895e174de85766`.
Source commit: `d0d5f2139a94f500a2cfacde75166e53315986dd`. New external analytic inputs: **NONE**.

This packet reuses finite `Finset.range`, `Finset.filter`, `Finset.min'`, `Finset.sigma`, finite cardinality/reindexing and signed sums from the pinned Lean/Mathlib standard library. It also reuses existing manuscript-internal `retainedOriginalSecond`, `retained_original_second_iff`, `hasRetainedOriginalSecond` and actual-root/quotient support from the existing source-only packets; their proof bodies have **not been compiled**.

No PNT, Mertens, BV, PNT-in-progressions, new Buchstab theorem, PP/same-rho assertion or analytic comparison has been re-proved. No external source supplies the original full/selected/inherited gate correspondence or count-source owner: those remain genuinely manuscript-INTERNAL and unresolved.

No axioms or target-equivalent inputs were added. There is no compilation, kernel replay or transitive-axiom audit; external dependency versions remain the ones pinned in the original `20261105-p5-h34-request-admission/EXTERNAL_INPUTS.md`. Inherited finite numerical guards remain **UNEVALUATED**.
