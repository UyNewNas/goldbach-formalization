# P1.4 checkpoint — actual original87 eighth-coordinate cutoff

Base: `9c4204245274e959fa28ad1dbc5833fb560ee3c3`. Branch: `chatgpt/p1-full87-eighth-cutoff-20261105`.

## New internal candidate

The exact original87 source coordinate on the *actual owned eighth predecessor frontier* satisfies `cutoff=53/13824<t₈` (previous source lemma), and pinned `primeHistoryLogCoordinates_frontier` reconstructs `N^t₈=p_last`. Since `53*261=13833>13824`, the paper-internal exponent step gives **N < p_last^261** without a guessed cutoff or ceil/floor step. For an even target N, the same actual rough-universe prime avoids N, so p_last>=3. The prior `target_deletion_power_gap_sandwich` then yields `1-260/(p_last-1) <= deletion(N,p_last,hi) <= 1` at each owned rank-eight prefix. The original owner/trim and occurrence list are preserved, not redefined.

**Warning / exact unresolved issue:** ordinary parity continuations below the eighth frontier can have later, SMALLER last-exit primes. This bound cannot be inserted into their full exit series by identifying the prefix p_last with every deeper exit. Their rank-j square tests and positive-series tail still require a distinct same-source proof. No density asymptotic or reserve payment follows here.

Verification: `17982` finite real-log-guided BigInt power comparisons; algebraic 53*261>13824 and 53*260<13824 checked by JS. No Lean/Lake or kernel run; syntax/API may fail elaboration. No original87 saved numerical check, full imported closure, CI, Codex or independent review. SOURCE_ONLY/UNEVALUATED.

Next: establish the actual fixed-rank descendant last-exit square-test exponent and strictly rounded power threshold, then carry the target-prime factor through the original sign-sensitive ordinary continuation. Do not promote the rank-eight bound to deeper j.
