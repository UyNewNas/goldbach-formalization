# P5.6 → h34 — literal selected-complement square: future marked slots

Date: 2026-11-09 UTC. Independent branch `chatgpt/p5-h34-selected-complement-future-square-20261109`.
Prior independently confirmed HEAD: `10117120383f3da5a3212d8af4ef7ac4c58db6ab`, continuing the h34 chain beyond initial entry `0a3fa5aa639e74122fbef18be02f0ad6fa8a77a0`.
Mathematical source commit: `7065444ee5d9f99a13bc4d46120535808d2f7673`.
Source blob: `bd9b1a9a987f20c20c11c9c37354ea9bfa14b0cb`.
Source file: `docs/source-only/20261109-p5-h34-selected-complement-future-square/Part5OriginalH430SelectedSquareStage.lean` (172 lines).

**PARTIAL_SOURCE_INCREMENT / SOURCE_ONLY / UNCOMPILED / UNEVALUATED / FULL_H34_OPEN**.

## Original mathematical object and this increment

The pinned manuscript Section "Restricted distribution and the actual coefficient class" explicitly retains *both* the full-square `S_(j-1)+2t_j≤ell_aux` and the selected-complement-square `sum_(i∈I)t_i+sum_(i<j, i∉I)t_i+2t_j≤ell_aux` for unselected `j∉I`. The all-marked-past condition is the precise time when the two squares coincide. Replacing the selected test by the full test prematurely would weaken the real support condition.

New Lean declarations:
- `fullSquareLHS`, `selectedComplementSquareLHS`: these are the literal finite expressions, not invented coefficient or count owners;
- `selected_sum_past_future`, `full_sum_selected_and_unselected`: finite past/future and marked/unmarked partitions;
- `selected_square_eq_full_plus_future`: **exact identity** selected square = full square + `Σ_(i∈I\\range(j)) t_i`, with the future marked mass explicitly retained;
- `full_square_le_selected_square` and `full_square_lt_selected_of_future_positive`: correct direction when original logarithmic selected exponents are nonnegative, and strictness when future marked mass is positive;
- `selected_square_eq_full_after_all_marks`: exact equality if `I⊆range(j)`, not before;
- `selected_square_admission_implies_full` and `selected_square_admission_iff_full_after_all_marks`: exact admissibility consequences, respecting `j∉I` at the unselected consumer.

There is **no assumption that an arbitrary history Boolean filter is the actual count owner**; this source is a manuscript coefficient-support lemma and does not yet solve original upper H430 selected-count source matching. No original c/K, root norm 7/2, row norm 12, real alpha, physical Q, two tags, 430+11 or manuscript target is changed.

## Checks actually performed

- Existing repository permissions: authenticated admin/push confirmed.
- Latest h34 predecessor: `1011712` verified through remote branch head and commit chain before branching. Dedicated branch created without touching other h34 branches, P1.4/P3.6, main, CI or dependencies.
- Source commit `7065444` fetched from GitHub. Exact source blob `bd9b1a9`, 172 lines, 2 definitions, 8 theorem declarations (including two private helpers). Parent comparison: one new Lean file, 172 additions, zero deletions.
- Forbidden escape marker scan: no `sorry`, `admit`, `axiom` or `unsafe` proof mechanism.
- Local `lean`, `lake`, `elan` are absent; local DNS resolution for `github.com` unavailable. No actual Lean elaboration, compilation, kernel replay, transitive axioms or numerical430 check. An existing core CI success on another branch is not evidence about this file. **No COMPILED/green credit.**
- Source-only file not staged into a complete project import path; no heavyweight GitHub build was dispatched or CI configuration modified.

## Still open manuscript-local obligations

1. Match the actual frozen upper H430 full/selected/inherited **count owner**, historical prime word/index set, stage and physical Q; use the exact selected-square geometry only when its corresponding policy actually demands it.
2. Actual U3/U4 original selected-count and historical depth/root weights; signed q/tag capacities, U4 overlap, six rejected lanes and first-excluded Euler suffix.
3. Request-level Buchstab/retention and all-action CLOSED-CELL induction, base/switch/seed/floor, feedback-to-integral and Theta/count correspondence.
4. PP/same-rho original instances, native-history mass and one causal 430+11 nested refinement.
5. Fixed Lean/Lake compilation of newly added and upstream source-only dependencies, kernel replay, transitive axiom audit and numerical certification.

**Next:** locate the actual count-owner stage and selected index set in frozen manuscript source/production policy, apply this exact inequality there, then independently validate in the pinned toolchain. Avoid another abstract filter partition or signed q-source identity. Complete h34 manuscript-local proof is OPEN.
