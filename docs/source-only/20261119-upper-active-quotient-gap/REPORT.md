# P1.4 — integral Rosser quotient gap on the actual upper LONG fibre

## Verified recovery

Predecessor `c83c33f4f9202830bbc48d6299929d212f922949`, branch `chatgpt/p1-full87-long-prime-active-level-20261119-0310`, matched compare 0 ahead / 0 behind before creating this independent continuation branch. Read predecessor source (265 lines), REPORT, REGISTRY, INPUT_BOUNDARY, HANDOFF; upstream full-modulus-lattice, integer-window, live-z and original signed helper; actual `ActualSmallRosser.lean`, `RoughPrimeUniverse.lean`, `ChenInitialPrimeSource.lean`. Applicable root, docs/source-only and predecessor-packet AGENTS.md returned 404.

Frozen manuscript pin `9731290e8f53cffda44129906cde6a965eaa869b`, `paper/source/manuscript-body.tex`, fetched blob `d529bea2ecfcc74d64fc1664ac770a3becaa7c79`; eq:current-PP read from pinned lines. Repository `lean-toolchain` and `lakefile.toml` checked, pins unchanged.

## New exact manuscript-internal mathematical delta

Let `b=(p::pre).prod`, `a=(N-P)/b`, and `W_active` the PREVIOUS bounding carrier, which is the original complete-modulus lattice intersected with actual small-Rosser support and strict real level `a<L`. Membership in this carrier entails `b | N-P` and original integer half-open bounds `N-X*p <= P < (N+1)/2`.

1. Any member forces `b>0`: if `b=0`, divisibility forces `P=N`, contradicting the original strict upper-half endpoint. Therefore there is NO added positivity assumption.
2. Exact divisibility gives `a*b=N-P`. The strict integer half-window gives `2P<N`, hence `N<2*a*b`. Consequently `a>N/(2*b)` and the real Rosser level yields `a<ceil(L)`. The exact integer quotient is in `[floor(N/(2*b))+1, ceil(L))`.
3. On the SAME fixed fifth/sixth occurrence, `P |-> (N-P)/b` is injective on `W_active` (the exact multiplication equality recovers `N-P`, and the window has `P<=N`). Thus the existing active-card invoice has the explicit numerical envelope

   `card(W_active) <= ceil(L) - (floor(N/(2*b))+1)`

   with natural truncated subtraction and exactly one strict upper endpoint. This is a *computable envelope*, not an unconditional improvement of the prior active-card invoice. It may be much larger than the literal active count.

4. If `ceil(L) <= floor(N/(2*b))+1`, the ENTIRE bounding carrier is empty, and the ORIGINAL LONG term vanishes at every P. This can hold even if `2*L*b<=N` (the older real-size zero test) fails, due to integer spacing. The zero result is extended to the original `fifth.remainingAfter` List with its original signed fifth mass and occurrence multiplicities. This condition remains UNVERIFIED for actual producer instances.

The one-time original signed finite prime sum also inherits the explicit quotient-gap bound, via the existing tighter active-card invoice. Nothing is subtracted from two unrelated sieve estimates; the original PLUS beta, parent, fifth-power filter, full q and source are UNMODIFIED.

## Evidence and validation

- New Lean SOURCE_ONLY candidate: `P4AOriginalFull87UpperActiveQuotientGap.lean` (283 lines, 8 theorem declarations), blob `aa005117b166c9949cf5af111aff21f7dcf96c8d`.
- Deterministic Python Fraction diagnostic: 100,000 randomly constructed integer-window/lattice/strict-level instances; 0 violations of the quotient-gap cardinal bound. 69,919 had zero quotient-gap envelope; among those, 1,082 had `2*L*b>N` (cases not eliminated by the older real-size criterion). These tests do NOT instantiate actual fifth/sixth events, exact Rosser beta or Lean.
- The 283-line fetched source had 0 prohibited proof-escape token matches. Static scanning does not grant formal proof credit.
- `lean --version`, `lake --version`, `elan --version`: each exit 127 (command not found). No pinned toolchain or project dependency cache available, no import staging, elaboration, kernel replay, transitive axiom check, independent review or saved87 replay. Container's pre-existing `memory.max=4294967296` bytes was not altered and no Lean memory cap was set.
- Status: **SOURCE_ONLY / UNEVALUATED / UNCOMPILED**. Local mathematical derivation + uncompiled candidate only. The new zero condition has not been instantiated to the real upper producer; no new `o(H_N)` claim or paid reserve.
- No CI, Codex, main/master modification, dependency upgrade or resource escalation.

## Next exact obligation

Read the actual producer's real `L,X,z` values and `b=(p::fifth.selectedAfter).prod` at its real callsite. For each original sixth occurrence, discharge the integral quotient-gap condition if possible (one-time zero); otherwise retain the PREVIOUS active-card invoice, with the explicit quotient-gap envelope as an optional alternative for numerical upper certification. Do not pay both. Then handle the actual Rosser quotient's PP admission or a genuine signed primitive-discrepancy estimate, same physical rho/H_N, lower-half corrections, ordinary continuation integral, complete actualParent/saved87, RAW/BOTH/changed-tagged, and independent compiler/density reserves.

P1.4 parent remains YELLOW. No new verified asymptotic gain.
