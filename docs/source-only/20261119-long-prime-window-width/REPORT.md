# P1.4 actual upper-prime long Rosser invoice: integer interval width

## Recovery and actual sources
Predecessor **b33a5f20ece860b46df68a5995761b3c11fad0a2** on
`chatgpt/p1-full87-long-boundary-live-z-20261119-0013`.
Original frozen manuscript: `UyNewNas/chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b`,
`paper/source/manuscript-body.tex` blob `d529bea2ecfcc74d64fc1664ac770a3becaa7c79`.
Current P1.4 branch: `chatgpt/p1-full87-long-prime-window-width-20261119-0114`; source `P4AOriginalFull87UpperPrimeWindowWidth.lean`.
Read prior packet Lean/REPORT/REGISTRY/INPUT_BOUNDARY/HANDOFF, actual RoughPrimeUniverse,
actualSmallRosserPlus_abs_le_one in ImbalancedChen/ActualSmallRosser.lean,
original chenPrimePrefix in ImbalancedChen/ChenInitialPrimeSource.lean and
the actual long fibre in the preceding source-only proof packet.
No AGENTS.md was found in root/ImbalancedChen/docs/docs-source-only paths at predecessor.

## Mathematical delta (all SOURCE_ONLY candidates)
The preceding exact nonzero support of the SAME long Rosser prime fibre gives
`N-X*p <= P` and `2*P<N`. The current packet defines the **bounding-only**
integer interval `Ico (N-X*p) ((N+1)/2)` and proves candidate membership
for every nonzero original long fibre. Its Rosser quotient, original
PLUS-beta, real fifth-power filter, strict upper-half condition and
all zero-valued terms remain untouched.

Pinned `actualSmallRosserPlus_abs_le_one` bounds each original nonzero
fibre in absolute value by one. A finite triangle inequality plus prime-prefix
subset cardinality yields

  |sum_{P in chenPrimePrefix N} Long_N(P,p)|
      <= card(Ico (N-X*p) ((N+1)/2)).

For **even N**, exact natural-number arithmetic gives the useful linear
positive-part bound

  card(Ico (N-X*p) ((N+1)/2)) <= X*p - N/2  (Nat subtraction).

The original signed fifth mass may be factored out, and swapping the same
prime prefix with the ordered fifth.remainingAfter list gives the candidate

  |sum_P sum_{p in actual remainingAfter} signedMass * Long_N(P,p)|
      <= sum_{p in actual remainingAfter} |signedMass| * (X*p - N/2)_+.

This is a genuine finite **absolute budget** for the actual unpaid boundary,
NOT a signed cancellation argument and NOT an H_N, o(H_N), or physical-reserve
payment. No new source policy, mask, auxiliary theorem-shaped structure, PP
input, or changed/tagged cover is introduced.

## Checks and limitations
Local `lean --version`, `lake --version`, `elan --version` exited **127**:
no pinned Lean executable, mathlib/native closure or source-only import staging
in the current environment. Memory cgroup reports 4294967296 bytes; no Lean
memory cap changed. Exact Python arithmetic diagnostic: 100000 seeded even-N
interval-width/excess cases with zero counterexamples; this tests only an
integer inequality, not real Rosser events or Lean type checking.
The candidate remains **SOURCE_ONLY / UNEVALUATED / UNCOMPILED**; not kernel
replayed, not transitively axiom checked, not independently reviewed, not
saved87 numerical certified. No CI, Codex, user machine, new resources or
main/master modification. All frozen pins and c,K remain unchanged.

## Next exact dependency
First stage the original source-only imports and compile with the pinned
Lean v4.33.0-rc1/mathlib e4c9178/native 09b97db toolchain if present in a
permitted environment. Then bind actual producer X and z and estimate
the **same** sum of positive parts against H_N; a prime-counting theorem
may not be invented or mislabelled as frozen smooth PP.
If a justified 2Xz<=N holds, the previously proved candidate zero
replaces this finite budget; it must not be paid twice.
After that: Rosser quotient PP adaptation, lower-half primitive/modulus-prime/
centre, ordinary same-rho residual integral, actualParent/full87 certificates,
RAW/BOTH/rank9/changed/tagged and separate compiler/density reserves.
P1.4 remains YELLOW.
