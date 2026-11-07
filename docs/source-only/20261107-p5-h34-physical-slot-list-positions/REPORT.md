# P5.6 → h34 — actual physical-slot rank-two LIST positions

Date: 2026-11-07.
Branch: `chatgpt/p5-h34-request-admission-20261105`.
Verified previous head: `6c0bfa2ee2c667d6ddd7a6aafe80ae149913f47b`.
New mathematical source commit: `fff01f56df706057d5741a203d302530aab4f378`.
Fixed manuscript: `UyNewNas/chen-imbalanced-semiprimes@ba6ec11d800eccc54406490631895e174de85766`,
`paper/source/manuscript-body.tex`, blob `d529bea2ecfcc74d64fc1664ac770a3becaa7c79`.
Lean: `v4.33.0-rc1`; Mathlib: `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`.

**PARTIAL_SOURCE_INCREMENT / SOURCE ONLY / UNCOMPILED / UNEVALUATED.
Complete manuscript-internal h34 remains OPEN.**

## What changed

The previous `Part5OriginalH430PhysicalSlotCollisionLedger` proves candidate
equality of rank-two STATE VALUES for equal actual physical (Q,p,ell)
slots and retains original q/tag surplus. It explicitly does NOT have
literal LIST OCCURRENCE POSITIONS.

The new `Part5OriginalH430PhysicalSlotListPositions.lean` (149 lines,
3 public candidate theorems, 1 private proof and 2 definitions; blob
`d648a49cc363261e003a01255ede9d3ec69c2931`) advances that precise
missing link:

1. `actualPhysicalRankTwoList` evaluates the existing genuine
   `firstExitDepthFrontier 2` under **one physical Q at a time**, with
   the original Rosser policy, 1/(r-1), and unchanged rough-prime carrier.
2. `member_has_fin_position` proves a concrete Fin-bounded position
   for a member of ANY list by structural induction. It assumes no
   Nodup, no historical quotient, and no `List.toFinset` conversion.
3. `observed_slot_has_actual_rank_two_position` instantiates the
   previous ACTUAL original tagged q receiver supplier. It first
   selects a real retained prime factor ell | q using
   `chosen_second_factor_spec`, connects the real rank-two frontier
   via `retained_original_second_iff_actual_rank_two`, recovers the
   physical (Q,p,ell) slot using `chosen_key_physical_source`, and
   then chooses an actual `Fin frontier.length` index with prefix
   `[ell,p]`. There is no invented q-as-prime assumption.
4. `observedSlotRankTwoPosition` makes the bounded position choice
   available to downstream source-only consumers, and
   `observed_slot_rank_two_position_prefix` checks its prefix.
5. `same_actual_position_forces_same_prime_pair` proves that, under
   one fixed Q, one ACTUAL position cannot independently have two
   distinct ordered (p,ell) prefixes.

This is a new, literal **LIST POSITION witness** rather than only a
state-value witness. It does not assert the chosen index is unique,
that full/selected/inherited filters retain the index, that different
Q histories form one mass pool, or that one index pays one q/tag
receipt. All actual q multiplicities, U3/U4 overlap, and two surplus
lanes from the preceding exact ledger remain intact.

## Source and verification

- GitHub source blob read back: `d648a49cc363261e003a01255ede9d3ec69c2931`.
- Compare previous head → source commit: exactly 1 added 149-line
  file, 0 modified files, 0 deletions, `ahead_by=1`.
- Source was submitted only to the h34-owned independent work branch,
  without force, merge, CI dispatch, toolchain upgrade or edits to
  P1.4/P3.6/production modules.
- Static scan found no `sorry`, `admit`, `axiom`, `unsafe`,
  `native_decide` or `run_tac` tokens. Raw bracket/parenthesis
  counts balance. These are NOT parsing, elaboration or proof checks.
- Lean/Lake executable not available in this environment. All new
  proof bodies and inherited finite table guards remain UNEVALUATED;
  there is NO kernel replay, transitive-axiom audit or independent
  mathematical verification. Source status is candidate/BLUE only.

## Exact remaining manuscript-internal duties

1. **Next action:** prove a genuine distinct-position injection or
   capacity upper bound for the chosen observed physical slots,
   using actual `Fin` indices and fixed-Q frontier LIST semantics;
   then apply the real `full/selected/inherited` filters to show
   which chosen indices survive. Do not assume state-value uniqueness
   implies list occurrence uniqueness. Preserve collisions/residual
   lane if any injection fails.
2. Match each surviving actual history position with original q/tag
   owner, root count weights, full selected/inherited multiplicities,
   z0/lower/upper and historical phases; do not pay once per q from
   one shared root or second factor.
3. Explicitly pay or bound surplus q, cross-tag collisions, cutoff,
   Rosser rejection, no second-factor and non-event lanes. Correct
   signed Euler direction remains an unproved manuscript consumer.
4. Complete request Buchstab/retention, all-action CLOSED-CELL count
   induction, base/switched/seed/floor/feedback-integral/Theta/count,
   manuscript-local PP/same-rho and native-history controls.
5. Produce one common nested 430+11 causal refinement, then stage,
   elaborate/compile, kernel-replay, audit transitive axioms and
   independently verify finite guards.

No new genuinely external analytic input. No new hypotheses equivalent
to h34 and no replacement of local manuscript responsibilities by
external inputs. Constants c/K, root norm 7/2, row norm 12,
true alpha, per-root same Q and complete q occurrence counts stay
unchanged.

**完整 h34 稿内证明仍未闭合。**
