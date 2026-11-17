# P1.4: direct sixthFromBoth absent from actual reduced 87-domain source

Baseline: `495a906a0f643975b5a1363018e83e9479714c85` on `chatgpt/p1-full87-fifth-integer-band-20261117-2110`.
Task branch: `chatgpt/p1-full87-no-direct-sixth-20261117-2215`.
New candidate source: `P4AOriginalFull87NoDirectSixthFromBoth.lean`, blob `78458a9c6962a4424b2daf3f55ebac95a448b16b`, source commit `7c2d36e30b17f51416b6c1704d2ef0647e1ba1eb`.

## Mathematical advance

The actual `fifthSixthWithoutBoth` source in `P4AOriginalFull87SixthBothInvoice.lean` branches on each real fifth candidate p of the original fourth state:

1. If just RAW or just LICENSED admits at fifth, it emits a genuine `.fifthExclusive` event retaining the exact fifth signed stopped subtree and its post-p carrier.
2. If BOTH admit at fifth, it calls `firstFifthEvents` on the original fifth child with `positive=false` and the original post-p carrier, removes inner events with `kind=.both`, then maps the others to `.sixthFromBoth`.

For the actual policies the sixth query has sign `!false=true`; both `P4AOriginalFull87CompleteSixthDispatch.policy_even` and `P4AOriginalFull87LicensedSixthPolicy.policy_even` return true on EVERY positive sixth prefix. Induction on the literal sixth carrier proves:

```
((firstFifthEvents R S h T pre false mass remaining).filter
  (fun ev => decide (ev.kind != .both))) = []
```

(the Lean source uses `≠`), without a new modulus bound or geometric mask. A second induction on the real fifth producer proves every occurrence in the already filtered source has constructor `.fifthExclusive`. The actual fourth-state parity follows from the existing original `real_fourth_prefix_positive` theorem, not an extra input. Final proposed event-level theorem:

```
actual_no_sixth_from_both ... state hstate fifthSelected inner :
  .sixthFromBoth fifthSelected inner ∉
    actualFifthSixthWithoutBoth ... state
```

**Crucial scope:** This eliminates a purported independent `sixthFromBoth` high-q tail **inside the already reduced event population**. It does NOT eliminate the original unfiltered sixth-`both` stopped terms by itself: that older removal relies on the independently existing `actual_rank_six_stopped_difference_zero_at_highq` proof candidate in `P4AOriginalFull87RankSevenStoppedHighQ`, which remains uncompiled. Nor does it imply `fifthExclusive` vanishes: its actual sixth-positive continuation, including the band `N^299 < b5^600`, remains unpaid. It adds no invoice and no numeric H_N saving.

Only original event List recursion was used. Order, occurrence multiplicity, complete a*b Rosser attachment, mass, signs and all existing three outside/producer invoices remain untouched. No new external number theory premise, axiom, target-equivalent field, or PP call.

## Exact checks and limitations

Remote GitHub source readback: blob `78458a9c6962a4424b2daf3f55ebac95a448b16b`, 166 source lines, forbidden construct scan no hit. Baseline compare after source commit: 1 ahead, 0 behind, only this file. Local commands `lean --version`, `lake --version`, and `elan --version` each returned **127 / command not found**. Local pinned project checkout and `.lake` dependency closure absent. Thus **SOURCE_ONLY / UNEVALUATED / UNCOMPILED**. Candidate tactics and elaboration have NOT been checked by Lean 4. No kernel replay, transitive axiom audit, real full-87 archive replay, or independent review. No CI dispatched, no Codex, no user machine, no toolchain change, no main/master write.

Frozen manuscript pin: `UyNewNas/chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b`, `paper/source/manuscript-body.tex` blob `d529bea2ecfcc74d64fc1664ac770a3becaa7c79`.
Lean `leanprover/lean4:v4.33.0-rc1`; mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`; native `09b97db5764ade1246bfb77206baa1b124760958`; c=49044063/25000000, K=8452171/1250000, unchanged.

## Next precise obligations

1. Same-rho signed quantitative payment for actual `fifthExclusive` events with `N^299 < b5^600`. Do not infer a PP level for high-q complete moduli merely from this necessary support condition.
2. Check the source-only original rank-six stopped-difference cancellation that was used when removing unfiltered sixth-`both`; the newly proved absence applies only AFTER that filtering.
3. Fixed-pinned Lean/Lake elaboration of both new and upstream source, kernel replay, transitive axiom audit and numerical archive verification separately.
4. RAW eighth, ordinary continuation/integral, density, full87 saved certificate, rank9, changed/tagged and independent reserve payments remain unresolved.

P1.4 parent: YELLOW.
