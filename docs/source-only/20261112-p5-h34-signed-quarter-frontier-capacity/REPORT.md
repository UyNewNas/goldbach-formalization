# P5.6 / h34 — original negative quarter: true finite-Q frontier capacity lower bound

Date: 2026-11-12 (Asia/Shanghai).
Repository: UyNewNas/goldbach-formalization.
Independent h34 branch: chatgpt/p5-h34-actual-nexttable-signed-source-residual-20261109.
Verified baseline: 10408a2cfd17b9ae105e1fdff071a94110f3850e.
Lean candidate source commit: eb2253a30755b152b98c62d27d49ae8220b72c1b.
Lean candidate source blob: d02f4401170680955382a9c4ed71e801c11a1c8b.
New file: Part5OriginalH430SignedQuarterFrontierCapacity.lean (177 lines, 2 definitions, 7 theorem candidates).

**PARTIAL_SOURCE_INCREMENT / SOURCE_ONLY / UNCOMPILED / UNEVALUATED / FULL_H34_OPEN**.

## Fixed scope

The old proof-map manuscript stays UyNewNas/chen-imbalanced-semiprimes at
ba6ec11d800eccc54406490631895e174de85766, NOT automatically switched
to the later release. Lean v4.33.0-rc1, Mathlib
e4c91783ca8e6a7c693ae624ade32fd22d4e43c1, original c/K, root
normalization 7/2, row normalization 12, true alpha, same-Q and 430+11
budget stay unchanged. P1.4, P3.6, CI and dependency files are untouched.

## Actual new manuscript-internal candidate proof increment

The preceding negative-quarter module proves an UPPER inequality on the
signed subtraction. That is the wrong orientation for the lower-sieve
goal. This module starts instead from the true ORIGINAL tagged unit
(p,q)-source, retaining the two tags in the U4 overlap.

Define two concrete capacities on the original observed physical Q set:
  C_slot = SUM over actual Q of card(observedPhysicalSlotsAtQ Q)
  C_frontier = SUM over actual Q of length(actualPhysicalRankTwoList Q).
Each Q uses its OWN literal firstExitDepthFrontier 2 list, and each
duplicate LIST occurrence is retained. No q/tag receipt is identified
with a whole frontier state; only ONE original representative per
observed physical (Q,p,ell) slot is placed at its actual Fin position.

Existing exact positional reindexing and original six-lane source ledger
give the candidate exact equality
  Upsilon3(N)+Upsilon4(N) = C_slot + L_six(unit).
The fixed-Q real-slot-to-position injection gives
  C_slot <= C_frontier,
hence the candidate count upper bound
  Upsilon3(N)+Upsilon4(N) <= C_frontier + L_six(unit).
Because the literal frozen Chen term is -(Upsilon3+Upsilon4)/4 on
BOTH original tags, the new candidate now has the correct LOWER sign:
  -(C_frontier+L_six(unit))/4 <= originalU34SignedQuarter(N).

Seven explicit candidate declarations:
- original_unit_position_sum_eq_q_slot_card
- original_unit_position_sum_le_q_frontier_length
- original_observed_q_slot_capacity_le_frontier
- original_unit_tagged_source_eq_actual_slots_and_six
- original_unit_tagged_source_le_frontier_plus_six
- original_negative_quarter_eq_slots_and_six
- original_negative_quarter_lower_by_actual_frontier_capacity

This is a real finite positional CAPACITY inequality in the correct
direction, but is NOT YET the quantitative Chen lower-sieve payment.
C_frontier may be much larger than the available selected-count budget.
L_six(unit) is explicitly unpaid. Nothing proves either to be small.
The old unit position mass H and original Euler first-excluded signed
weights are not substituted for an arithmetic q receipt.

## Engineering checks and limitations

GitHub verified source commit eb2253a30755b152b98c62d27d49ae8220b72c1b contains exactly one
new Lean candidate file, 177 lines, with blob
d02f4401170680955382a9c4ed71e801c11a1c8b. Its diff against
10408a2cfd17b9ae105e1fdff071a94110f3850e is additive and does not touch other tasks. A text scan
of the re-read source found no proof placeholders, unsafe declarations
or new custom axioms.

The execution container has no Lean, Lake or Elan executable, no
installed source-only transitive import closure, and no successful
native GitHub network path. No Lean/Lake module compilation, kernel
replay, transitive axiom audit or finite certificate replay ran.
A successful GitHub blob comparison or static scan is NOT proof
verification. All seven statements remain CANDIDATE_UNCOMPILED,
and no green node is awarded.

## Manuscript-internal unresolved obligations

1. Control the ACTUAL summed rank-two frontier lengths C_frontier
   quantitatively by the appropriate original full/selected/inherited
   owners and ROOT 7/2 weight, not arbitrary whole-list capacity.
2. Pay all six original q/tag collision/rejection lanes with the
   correct Chen negative coefficient, U4 double-tag accounting,
   signed Euler suffix and real historical multiplicity.
3. Pay q-fibre physical source residual and selected-row errors,
   establish actual Q80 base/switched/seed/floor and predecessor
   CLOSED-CELL count induction.
4. Complete manuscript-local PP/same-rho, native-history weights,
   integral/Theta/count bridge and one coherent 430+11 causal
   nested refinement.
5. Stage source-only imports using exact pinned toolchain, genuinely
   compile new and direct dependency modules, kernel replay and audit
   transitive axioms and numerical certificates.

NEXT: replace the crude full frontier-length capacity by the REAL
filtered full/selected/inherited paid capacity and prove corresponding
signed six-lane upper cost; do not recast these as external analytic
assumptions. When staging is possible, compile this exact packet.
Complete h34 manuscript-internal proof is STILL OPEN.
