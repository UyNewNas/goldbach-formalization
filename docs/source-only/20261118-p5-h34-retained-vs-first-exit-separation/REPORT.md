# P5.6 → h34 — real retained vs first-excluded source separation

Date: 2026-11-18.
Repository: UyNewNas/goldbach-formalization.
Dedicated continuation branch: chatgpt/p5-h34-full-tagged-actual-fin-20261112.
Exact parent: c9c8651d4f882636d0eab6894d5226d8cbab54f1.
Frozen manuscript: UyNewNas/chen-imbalanced-semiprimes@ba6ec11d800eccc54406490631895e174de85766.
Lean v4.33.0-rc1; Mathlib e4c91783ca8e6a7c693ae624ade32fd22d4e43c1.

STATUS: SOURCE_ONLY / CANDIDATE / UNCOMPILED / UNEVALUATED / FULL_H34_OPEN.

## New manuscript-internal increment

Part5OriginalH430RetainedVsFirstExitSeparation.lean imports the
previous actual first-compatible frontier factor and the previously
implemented physical-Q unique first-excluded history ledger.

The previous canonical retained-prefix packet selects a least
ordinary-Rosser-compatible q divisor of an ORIGINAL strict source
receipt. The independently implemented signed first-exit packet,
however, counts FROZEN-ONLY and STILL-FROZEN-REJECTED arithmetic
receipts. They are not two alternative owners for the same original
q/tag receipt.

The new proof bodies:
1. Derive originalTagged membership for stageRetainedOriginal.
2. Prove retained receipts cannot enter frozenFailAtActualQ, using
   the frozenOnly = frozenTagged \ originalTagged definition.
3. Prove retained receipts cannot enter rejectedFailAtActualQ,
   using the EXISTING original-to-frozen sieve inclusion and its
   exact N/tau/n hypotheses.
4. Establish disjointness of the whole stageRetainedOriginal
   and actualQFailSource, and every canonical retained-prefix
   fibre versus actual-Q signed first-exit failure fibre.
5. Preserve arbitrary additive signed q/tag weights in the
   disjoint two-family arithmetic fibre partition.
6. Rewrite the first-excluded family as ONCE-PER-(Q,p,ell)
   signed historical exit plus exact, expressly UNPAID source
   remainder, retaining the canonical strict-original receipts.

This is a precise unmatched RECEIPT lane, not a statement that
all history first-exit/first-forbidden states are absent for
strict-original retained paths. Historical state projection
can collide even where receipt sets are disjoint. Neither a
root-7/2 selected count bound nor a q-to-Fin owner is introduced.

## Validation and engineering

Created in a new source-only directory; no existing P1.4, P3.6,
CI, math production source, toolchain or manuscript file is edited.
The initial 20261105 REPORT/REGISTRY/EXTERNAL_INPUTS and its
local source were reread; actual branch HEAD, previous source and
current source-only first-excluded ledger were checked before write.
Original cutoff assumptions remain explicit.

Local runtime has git but no lean/lake/elan or pinned source-only
import closure. Native github.com DNS lookup failed. GitHub connector
push access and branch revision were confirmed. No Lean/Lake
compilation succeeded; no kernel replay or transitive axiom audit
was performed, and finite certificates remain UNEVALUATED. Static
source checks must not be described as Lean validation.

## Open manuscript-internal obligations

1. Establish any legitimate CROSS-SOURCE history relationship between
   retained first-compatible rank-two frontier and deeper actual
   first-forbidden states; the two disjoint arithmetic source lanes
   cannot be equated receiptwise.
2. Original full/selected/inherited owner filters, per-(Q,p,ell)
   q/tag collision capacity and true root norm 7/2.
3. Strict-prime Buchstab/retention positive sources and full
   base/fixed/switched/seed/floor CLOSED-CELL induction.
4. PP/same-rho, native-history, signed Euler remainder payment,
   integral–Theta–count and common 430+11 nested causal realization.
5. Stage pinned imports, real Lean/Lake incremental compilation,
   kernel replay, transitive axioms and finite certificate audit.

FULL h34 manuscript-internal proof remains OPEN.
