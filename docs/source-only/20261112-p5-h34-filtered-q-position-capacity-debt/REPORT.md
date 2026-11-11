# P5.6 / h34 — true filtered Q-position capacity, with erased q-source debt

Date: 2026-11-12 (Asia/Shanghai).
Repository: UyNewNas/goldbach-formalization.
Dedicated h34 branch: `chatgpt/p5-h34-actual-nexttable-signed-source-residual-20261109`.
Verified prior HEAD: `6e2ca04cfa0608a3170c56bc6844a48c53e8294e`.
This packet's Lean source commit: `49abdb306d43250f8c685adb1e14b10c71240433`.
New source: `Part5OriginalH430FilteredQPositionCapacityDebt.lean`.
Source git blob: `b165d3e52fa8145ff69edf4c2580a2ba73176d3f`.
Source: 202 nonblank-or-terminated diff lines, 3 definitions, 9 candidate theorems.

**PARTIAL_SOURCE_INCREMENT / SOURCE_ONLY / UNCOMPILED / UNEVALUATED / FULL_H34_OPEN.**

## Frozen scope and source provenance

The manuscript stays `UyNewNas/chen-imbalanced-semiprimes`
at `ba6ec11d800eccc54406490631895e174de85766`, exactly as the existing
proof mapping specifies. Lean `v4.33.0-rc1`, Mathlib
`e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`, original c/K,
root weight `7/2`, row norm `12`, true alpha, same-Q roots,
full/specified-cell vs scalar read distinctions and the 430+11
budget are unchanged. P1.4/P3.6, other tasks' files, and CI are untouched.

The preceding source `Part5OriginalH430SignedQuarterFrontierCapacity`
gave the Chen negative-quarter lower direction, but charged the COMPLETE
rank-two list length at every observed physical Q. This new packet
reuses the actual existing `FixedQPositionFilterLedger` fixed-Q
slot injection, the exact slot erasure partition, and the earlier
`QDependentPositionErasure` semantics. No source-only import closure
has been installed or compiled.

## Actual manuscript-internal increment

For an arbitrary **Q-dependent** Boolean post-frontier filter `keep Q`,
define the following REAL, concrete sums over the existing
`observedReceiptQs`:

- `F_keep`: cardinality of the *actual surviving Fin list positions*
  at each Q, separately counted at that Q.
- `S_keep`: number of *observed physical (Q,p,ell) slots* whose
  chosen Fin position survives.
- `E_erase`: number of *observed physical slots* erased by the
  chosen filter. This is original arithmetic-source debt, NOT
  erased historical mass.

The prior literal per-Q slot erasure partition proves the candidate
equality `C_slot = S_keep + E_erase`. The prior actual injection into
kept positions proves `S_keep <= F_keep`. Therefore:

    C_slot <= F_keep + E_erase.

The exact original U3/U4 tagged source ledger (both original tags
retained in U4 overlap) already established:

    Upsilon3(N) + Upsilon4(N) = C_slot + L_six(unit).

The new consumer yields:

    Upsilon3(N) + Upsilon4(N)
      <= F_keep + E_erase + L_six(unit).

Hence the ORIGINAL signed Chen quarter now has the proper lower
orientation with the *filtered* history capacity:

    -(F_keep + E_erase + L_six(unit))/4
      <= -(Upsilon3(N) + Upsilon4(N))/4.

Neither `E_erase` nor the six original rejected/collision lanes
is suppressed or assumed small. All positional counts are literal
per-Q Fin occurrences, NOT quotiented physical states or q/tag
arithmetic counts. A q representing several original receipts
is not silently assigned to one historical unit.

The new source also proves the candidate inequality `F_keep <=
C_frontier`; this does NOT imply an improvement in the total paid
quantity until `E_erase` is quantitatively controlled. It checks
the actual ordinary Rosser **full-prefix gate** of the current
rank-two recursion: this gate erases no observed slots and keeps
all existing positions. That ordinary gate is NOT the manuscript's
complete full/selected/inherited count-owner filter.

## Exact new declarations

Definitions:
1. `actualFilteredQPositionCapacity`
2. `actualErasedQSlotDebt`
3. `actualKeptQSlotCapacity`

Candidate theorems:
1. `actual_observed_q_slots_eq_kept_plus_erased`
2. `actual_kept_q_slots_le_filtered_positions`
3. `actual_observed_q_slots_le_filtered_plus_erased`
4. `actual_filtered_q_capacity_le_full_frontier`
5. `original_unit_source_eq_filtered_slots_erased_and_six`
6. `original_unit_source_le_filtered_positions_with_all_debts`
7. `original_negative_quarter_lower_by_filtered_position_debts`
8. `actual_ordinary_full_prefix_erased_debt_zero`
9. `actual_ordinary_full_prefix_kept_capacity_eq_frontier`

## Actual validation boundary

GitHub write result was fetched back: source commit `49abdb3`,
blob `b165d3e52fa8145ff69edf4c2580a2ba73176d3f`, diff `+202/-0`,
with exactly one new path relative to `6e2ca04`. Static source
scan found no `sorry`, `admit`, new `axiom` or `unsafe`.
These are text and Git object checks only.

In the current execution container `lean`, `lake`, and `elan`
are not on PATH. Native `git ls-remote` failed with DNS failure
resolving github.com. The pinned source-only transitive import closure
is not available locally. No Lean/Lake parsing, elaboration, module
compilation, kernel replay, transitive axiom audit, table replay,
or this-module CI execution was performed. All 9 theorem declarations
remain **CANDIDATE_UNCOMPILED**, and zero engineering green credit
is claimed. Other CI success on different modules cannot validate
these source-only files.

## Remaining manuscript-internal obligations

1. Derive the ACTUAL manuscript full/selected/inherited **Q-dependent**
   count-owner filter from frozen U3/U4 arithmetic predicates, not a
   freely supplied Boolean function; prove its quantitative
   `F_keep` capacity with original root weight 7/2.
2. Pay `E_erase` and all six literal q/tag collision/rejection
   lanes, with U4 double-tag accounting and correct signed
   first-excluded Euler suffix. An arbitrary Boolean erasure could
   erase all observed slots, so these debts cannot be set to zero.
3. Pay q-multiplicity physical source residual, selected-row error
   and actual predecessor CLOSED-CELL recursion, including
   base/switched/seed/floor, correct original q receipts.
4. Prove manuscript-local PP/same-rho, native history and outer
   integral–Theta–count identity with one 430+11 causal refinement.
5. Stage the pinned dependency closure, incrementally compile,
   kernel replay, transitive-axiom audit and finite certificate
   verification.

**NEXT:** identify the real original full/selected/inherited gate
at each physical Q, then instantiate the present filtered positional
source inequality with that *proved* gate and pay its erased-slot
arithmetic debt and six original lanes. Before relying on any
candidate declaration, stage and compile with the frozen Lean/Mathlib
versions. The complete h34 manuscript-internal proof remains OPEN.
