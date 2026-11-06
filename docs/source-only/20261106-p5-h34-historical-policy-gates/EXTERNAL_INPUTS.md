# P5.6 / h34 — external-input boundary (historical-policy-gates packet)

Pinned manuscript: `UyNewNas/chen-imbalanced-semiprimes@ba6ec11d800eccc54406490631895e174de85766`;
source body blob: `d529bea2ecfcc74d64fc1664ac770a3becaa7c79`.
No new analytic theorem and no new foundational axiom were supplied.

## Actually consumed

- Lean/Mathlib standard `List` membership and append structure, `Bool`,
  `Nat`, `Real`, proposition decidability, conjunction and equivalence.
  Uses the same repo-pinned Lean/Mathlib version; no external proof is reimplemented.
- Internal existing `ImbalancedChen.FirstExitCandidateGeometry`
  (`mem_firstExitNextSelectionCandidates_iff`,
  `actualPrimeNextSelection_geometry`),
  `ImbalancedChen.RoughPrimeUniverse`
  (`mem_roughPrimeUniverse_iff_of_cutoff_le_cap`), and
  `ImbalancedChen.ActualFrozenFrontierDensity`
  (`actualPrimeFrontier_geometry`) at the original repo version.
- Internal `ImbalancedChen.OrdinaryRosserFirstExitPolicy`
  (`ordinaryRosserRetainedPolicy` and `ordinaryRosserPrefixAdmissible`).
- Uncompiled **manuscript-local source-only** `Part5OriginalH430HistoricalCandidateOrder`,
  `Part5OriginalH430PhysicalCutoffOwnerOrder`, and earlier actual U3/U4
  tagged rejection/first-bad modules. Their definitions are reused, not
  promoted to external proof licences.

## Still manuscript-internal

True full/selected/inherited owner and counting identity, universal
physical cap compatibility, exact signed rejection mass and multiplicity,
all-action closed-cell/Buchstab/retention, base/seed/floor, PP/same-rho,
native-history/Theta and one 430+11 nested refinement.

The wrapper's explicit history frontier membership, cutoff bound and
arithmetic receiver hypotheses are LOCAL geometric conditions, not
unverified assertions of the h34 goal. No external PNT/Mertens/BV
proof is generated and no new distribution theorem is assumed.
