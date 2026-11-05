# P1.4 fixed-rank odd-exit checkpoint — 2026-11-05

Parent verified: `7036ae5256511944cf69ad5938504416888d4849` (branch `chatgpt/p1-full87-eighth-cutoff-20261105`).
Continuation branch: `chatgpt/p1-full87-fixed-rank-exit-20261105`.
New source: `docs/source-only/20261105-full87-fixed-rank-exit/P4AOriginalFull87FixedRankExit.lean`.
Source Git blob SHA: `d1b6458855a1dda47f12a5fdc22f90f4f8d25d0f`.

**Status: SOURCE_ONLY / UNCOMPILED / UNEVALUATED / ZERO KERNEL CREDIT.**

## This run's original manuscript-internal result
For a descending real prime-log sequence t_0,...,t_(2m), let S_(2k)=sum_(i<2k)t_i.
If every prior odd *full-square* test at the SAME frozen beta level passes,
S_(2k)+3t_(2k)<beta (k<m), and the first odd exit fails,
beta<=S_(2m)+3t_(2m), then beta <= 3^(m+1)*t_(2m).
Proof: S_(2k+2) <= S_(2k)+2t_(2k) < (S_(2k)+2beta)/3.
Thus beta-S_(2m) >= beta/3^m; the failed exit gives the conclusion.
The bound is stronger than the manuscript's beta/(3*2^(j-1)) at j=2m+1.

For a prime p_last=N^t_last and a frozen beta>=betaFloor>0,
the fixed integer K is allowed if 3^(m+1)<betaFloor*K, yielding N<p_last^K.
The existing EXACT target-prime deletion multiplier is then bounded below by
1-(K-1)/(p_last-1) (or 1-K/(p_last-1) in the concrete conservative wrapper).
No PNT/BV/Mertens statement enters this algebra.

For *actual* original87 owned eighth histories with RealizedHistory, original
trim/source and adequate cap resolution, both the own-sixth actualParent and
the new *rounded* finiteCap are >9*(53/13824).  Hence the fixed integer
30*3^(m+1) has strict level room, independently of N.  A concrete wrapper
uses k=30*3^(m+1) as its conservative deletion-cardinality budget.

## Crucial unfinished same-source proof
The concrete wrapper requires actual deeper continuation data: all prior odd
full-square tests at the identical frozen beta, their processing-order
nonincrease, the first failed test, and the exact last-prime log reconstruction.
These are **not** extracted from original ordinaryParityRosserPolicy yet.
An eighth-rank prefix membership by itself does NOT justify them; inherited
earlier ranks may have been tested at *different* historical levels.

Next action: prove the actual descendant guard-extraction lemma for the two
ordinary continuations, distinguishing pre-eighth inherited tests from
post-eighth fixed-level tests; prove that the original full/complement
squares transport to either frozen level before applying this wrapper.
If the same-level tests do not hold, revise the fixed-rank normalization and
record an explicit counterexample rather than treating the wrapper as usable.

Source manuscript: `UyNewNas/chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b`,
`paper/source/manuscript-body.tex`, original blob
`d529bea2ecfcc74d64fc1664ac770a3becaa7c79`.

Validation this run: exact Fraction randomized successful-prefix 10,093,
first-exit cases 8,359; exact target-factor cases 172,368; independent LP
extremal checks for odd ranks 1,3,...,15 (floating solver, diagnostic only).
Strict 30*9*53/13824 - 1 = 9/256 checked exactly.  No Lean/Lake parser,
compiler, kernel replay, original saved-87 certificate run, transitive axiom
audit, CI dispatch, Codex, or independent review.

Fixed toolchain remains Lean v4.33.0-rc1,
mathlib e4c91783ca8e6a7c693ae624ade32fd22d4e43c1,
subfish-zhou/goldbach-lean@09b97db5764ade1246bfb77206baa1b124760958.
