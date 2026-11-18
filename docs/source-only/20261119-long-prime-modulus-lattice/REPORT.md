# P1.4 actual long prime window: complete-modulus lattice refinement

## Verified recovery
Read previous packet on `chatgpt/p1-full87-long-prime-window-width-20261119-0114`, final commit `47579a6907e980ae18b5bc83e768bf157c02951e`: full Lean source, REPORT, REGISTRY, INPUT_BOUNDARY and HANDOFF. Read linked original UpperPrimeLiveZWindow, UpperPrimeShortBoundary, UpperHalfPrimeFibre, StoppedGlobalPrimeLedger, PlusBetaPowerFilter, FirstFifthStoppedEvents and ActualSmallRosser, ChenInitialPrimeSource, RoughPrimeUniverse. Checked pinned manuscript blob d529bea2ecfcc74d64fc1664ac770a3becaa7c79. Repository tree reported no AGENTS.md. This branch starts from the verified 47579a6; no reset to 9649ab3.

## Exact manuscript-internal delta (candidate)
The old invoice counted all integer P in [N-X*p, (N+1)/2). For the SAME original nonzero upper-half LONG fibre, its complete divisor is b=(p::pre).prod and its original quotient a=(N-P)/b satisfies a*b=N-P. Therefore b divides N-P. The new bounded carrier is

  W_mod(N,X,pre,p) = {P in [N-X*p, (N+1)/2) : b | (N-P)}.

This is a strict arithmetic subset of the previous interval and is NOT inserted into the definition of the source summand. Candidate proofs establish:
1. nonzero original fibre implies exact full-modulus divisibility and P membership of W_mod;
2. absolute original prime sum <= card(W_mod), using actualSmallRosserPlus_abs_le_one, without prime distribution;
3. card(W_mod) <= card(old window), so the new estimate *replaces* the older width invoice (no double payment);
4. for the SAME original signed fifth mass and ordered remainingAfter List, absolute prime-first sum <= sum of per-occurrence signed-mass times card(W_mod), preserving repeated occurrences.

No Rosser support, beta, prime complement, strict X/high-q endpoint or fifth-power filter is removed from the actual original summand. No geometry-zero assertion is used as arithmetic zero and no new asymptotic saving is claimed. This is finer than raw width but may still be much too large relative to H_N.

## Diagnostics and environment
- Actual pinned repository lean-toolchain: leanprover/lean4:v4.33.0-rc1.
- Actual lakefile.toml pin: mathlib e4c91783ca8e6a7c693ae624ade32fd22d4e43c1 and goldbach 09b97db5764ade1246bfb77206baa1b124760958.
- Checked system command lookup for lean/lake/elan: none found; no matching local dependency closure or import staging. No Lean/Lake execution, hence SOURCE_ONLY / UNEVALUATED / UNCOMPILED.
- Existing memory.max is 4294967296 bytes, not a Lean limit added by this run; no memory or tooling changes.
- Python exact integer diagnostic: 40000 deterministic (N even, X,p,b positive) random interval/lattice comparisons, 0 violations of lattice cardinal <= interval cardinal; 39173 strict improvements. The diagnostic only tests the combinatorial envelope, not the actual tree, primality or Lean elaboration.
- No kernel replay, transitive axiom audit, saved87 replay, numerical H_N certification, independent peer review, CI, Codex, main/master edit or resource escalation.

## Exact remaining obligations
Compile candidate with pinned Lean/dependencies and correctly staged source-only imports if that toolchain is present in an authorized local runtime. Determine actual producer X upper bound, real upper z and its pinned rho0 mapping; if 2Xz<=N is proved use prior exact zero rather than a second reserve invoice. Otherwise estimate actual full-modulus lattice counts times original fifth signed masses relative to H_N. The Rosser quotient retains a discrete arithmetic filter not licensed by smooth PP. Continue original lower-half primitive/modulus-prime/centre, ordinary integral, actualParent/full87/saved87, RAW/BOTH/rank9 changed/tagged and separate compiler/density reserves. P1.4 parent remains YELLOW.
