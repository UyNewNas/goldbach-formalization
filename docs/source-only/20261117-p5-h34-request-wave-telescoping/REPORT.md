# P5.6 → h34 — actual request wave residual telescoping

Date: 2026-11-17.
Previous verified same-task head: `4c3ca0abf3312ea9c9ceff1a6e9e754f446ebcb2`.
Source commit: `8ecfbee44724beacfb65e1f23fd0c04d6e2f400c`.
Branch: `chatgpt/p5-h34-full-tagged-actual-fin-20261112`.
Pinned manuscript: `ba6ec11d800eccc54406490631895e174de85766`.
Status: **PARTIAL_SOURCE_INCREMENT / SOURCE_ONLY / UNCOMPILED / UNEVALUATED / FULL_H34_OPEN**.

## What is actually new

`Part5OriginalH430RequestWaveTelescoping.lean` builds on the existing actual
`RequestedBranches`, `RequestedHistory`, and `ActualRequestAllActionWave`.
No additional alternative request resolver, owner predicate or receipt filter is
defined. It does not repeat the older literal all-action level partition.

For any real-valued diagnostic `F (remaining) (Request)` define:

* `terminalSeed F`: `F 0 r` only at genuine generation zero.
* `localDefect N Q F (g+1) r`: current diagnostic minus the sum of
  **actually selected** next-request diagnostics with **literal** edgeWeight.
  Zero generation has zero local defect.
* `positiveDefect`: maximum of the actual signed defect and zero, explicitly
  recording an unpaid, nonnegative local discrepancy.

The principal unconditional proof body `root_eq_terminal_plus_defects` is
the exact telescoping formula:

    F g r =
      waveAccount N Q g r (terminalSeed F)
      + waveAccount N Q g r (localDefect N Q F).

The proof is by induction on the original remaining generation and the
`wave_successor` identity, not by assuming a final count inequality.
`waveAccount_mono` uses the existing `mark_pos` theorem. Therefore
`root_le_terminal_plus_unpaid_defects` obtains the exact unapplied
one-sided residual budget with `positiveDefect`, without asserting its
smallness or converting it into a Chen count bound.

Three further candidate theorems calculate the local defect on the literal
selected retention, Buchstab, and 106-bank branches. The retained branch
keeps its specified cell; the Buchstab branch keeps the strict original
prime-child carrier, with scalar successor requests; bank uses its actual
`actionOfSlot` with W1/W2 weights. Each original list occurrence remains
distinct, including multiple identical physical products.

## Exact boundary

No one-step quantitative Buchstab estimate or retained closed-cell
inequality has been proved here. The `positiveDefect` sum is a **visible
unpaid obligation**, not a paid error or an external theorem. The
`F` diagnostic remains arbitrary. This packet does not identify `F` with
the frozen original U3/U4 arithmetic count, claim full/selected/inherited
ownership, pay multiple q/tag receipts by the root norm 7/2, or supply
base/switched/seed/floor, PP/same-rho, native-history or 430+11 integral
refinement. CLOSED-CELL quantitative induction is still OPEN.

Fixed original constants c/K, norm7/2, row norm12, real alpha, same physical
Q, separate cell/scalar reads, all original receipt multiplicities, and
430+11 nesting remain unchanged. P1.4 and P3.6 are untouched.

## Validation, engineering and next handoff

GitHub write permission checked (admin), existing dedicated branch head
re-read before both writes; no active Actions runs were reported for this
branch. No force push, merge, CI change, dependency upgrade or external
analytic lemma was made. Final SHA and actual diff must be checked from
GitHub after this metadata update.

Local execution environment: `command -v lean`, `lake`, `elan`
all returned no executable; `getent hosts github.com` returned no DNS
result; source-only transitive `ImbalancedChen/` installation was not
materialized. Therefore **no Lean compilation, kernel replay, transitive
axiom audit or finite certificate replay has occurred**; no green state.
Simple text scanning is not elaboration or a proof check.

Pinned toolchain: `leanprover/lean4:v4.33.0-rc1`.
Pinned Mathlib: `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`.

Next specific step: stage the fixed source-only closure under
`ImbalancedChen/`, compile this module and its actual history/wave
dependencies, repair any elaboration errors. Then specialize `F`
to the real selected CLOSED-CELL count diagnostic and use genuine
request-level Buchstab/retention quantitative bounds on the explicit
`positiveDefect` terms, not on an invented scalar owner.
