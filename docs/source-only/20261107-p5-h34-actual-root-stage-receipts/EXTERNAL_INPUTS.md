# P5.6 h34 — pinned external-input boundary for actual root-stage receipts

Status: SOURCE_ONLY / UNCOMPILED / UNEVALUATED.
Original manuscript pinned to
UyNewNas/chen-imbalanced-semiprimes@ba6ec11d800eccc54406490631895e174de85766,
paper/source/manuscript-body.tex, blob d529bea2ecfcc74d64fc1664ac770a3becaa7c79.

## External libraries actually reused

- Lean toolchain: leanprover/lean4:v4.33.0-rc1 (unchanged lean-toolchain).
- Mathlib pinned by unchanged lake-manifest.json to
  leanprover-community/mathlib4@e4c91783ca8e6a7c693ae624ade32fd22d4e43c1.
- Elementary Mathlib/Lean Finset filter/sigma/disjoint sum membership,
  card_disjSum, card_sigma, sum_disjSum, sum_sigma, reindexing, Nat casts,
  propositional simplification and real arithmetic are called in the source.
  These are not new number-theoretic proof inputs. Full transitive
  dependencies have NOT been audited and no claim of kernel verification
  is made.

No PNT, Mertens, BV, prime-distribution or new Buchstab statement is
added, proved or reclassified. No target-equivalent assumption is introduced.

## Existing manuscript-local interfaces used (NOT outsourced)

- Part5OriginalH430HistoricalPolicyGates.tagged_root_stage_ordinary_policy_iff:
  for z0 <= (cap:Real) and a genuinely rawTagged receiver, existence of
  an enumerated stage-zero candidate with selectedPrefix=[p] and the
  ordinary Rosser retained-policy test is equivalent to the real prime
  carrier/coprime/cutoff condition together with singleton Rosser
  admissibility. Used in original_stage_iff_physical_root.
- Part5OriginalH430ActualRootGateCoprime.raw_root_not_target:
  a rawTagged root p does not divide N, from actual primality and
  Nat.Coprime. Used in original_stage_iff_physical_root.
- Part5OriginalH430OriginalSelectedRootFibres.original_tagged_subset_raw_unconditional:
  the actual originalTagged receipts are inside rawTagged.
  Used in original_stage_iff_physical_root and
  actual_original_stage_requires_large_presieve.
- Part5OriginalH430PhysicalSelectedRootQFibres.originalPhysicalQ and
  original_physical_licence_iff: exact tag/p-specific Q and remaining
  strict root cutoff + singleton Rosser tests.
  Used in original_stage_iff_physical_root.
- Part5OriginalH430PhysicalSelectedRootQFibres.actual_physical_selected_count_three_terms
  and actual_physical_selected_signed_three_terms:
  exact prior three-way selected arithmetic source splits; now rewritten
  with genuine stage-zero historical candidate membership in
  actual_original_count_with_historical_root_candidates and
  actual_original_signed_with_historical_root_candidates.
- Part5OriginalH430OriginalRootCutoffObstruction.raw_strict_root_requires_large_presieve:
  genuine selected U3/U4 p begins at N^a, so accepted strict historical
  roots require N^a < z0. Used only with its actual candidate premise
  in actual_original_stage_requires_large_presieve.

These source-only imported theorems themselves remain UNCOMPILED, so
their stated signatures and proof bodies have not passed Lean checking.

## Still manuscript-internal

Actual source full/selected/inherited and owner multiplicity, root outer
weight, stage/cutoff choice, exception-lane payment, directional signed
Euler count comparisons, count CLOSED-CELL induction, integral/Theta
matching, genuine PP/same-rho consumer instantiation, native-history
quality and ONE common nested 430+11 causal refinement. None is
declared external and no external proof is attempted.
