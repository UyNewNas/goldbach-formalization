# P1.4 — frozen upper rho0 six-factor exponent specialization

## Recovery and actual source read
Predecessor task HEAD `66b3c8c890c41d7e56c8d5252c0838af6d5110f1`, branch `chatgpt/p1-full87-stopped-q0-rough-six-lower-20261118-1431`; verified by compare: identical (ahead=behind=0). Read its complete 240-line `P4AOriginalFull87StoppedQ0RoughSixLower.lean`, REPORT.md, REGISTRY.json, INPUT_BOUNDARY.md and HANDOFF.md, as well as the original `ImbalancedChen/RoughPrimeUniverse.lean`, actual rank-four, ordered suffix and fifth power-tail sources. AGENTS.md not found at root, docs, docs/source-only or previous packet. No concurrent changes identified at comparison time.

Isolated continuation branch: `chatgpt/p1-full87-rho0-six-cutoff-20261118-1510`. Frozen manuscript pin `9731290e8f53cffda44129906cde6a965eaa869b` / blob `d529bea2ecfcc74d64fc1664ac770a3becaa7c79` re-read: upper construction `rho0=19/96`; actual text `P_N(N^rho0)`. No pins, constants, main/master, CI or other task modified.

## Actual manuscript-internal mathematical increment
The prior packet proved `w^6 <= q0` is necessary for a nonzero actual sixth-PLUS full-modulus exceptional fibre, and cancelled the true signed stopped q0 at fixed `w` if `q0<w^6`; it did not prove any power-law instance. This packet discharges precisely the frozen upper numerical instance without a new assumption. At each fixed integer `N>=8`:
```
w := (N : Real) ^ (19/96)
w^6 = N^(19/16) > N > floor((N-2)/2) = q0.
```
Lean candidate uses pinned mathlib `Real.rpow_mul`, `Real.rpow_natCast` and `Real.self_lt_rpow_of_one_lt`; the exact integer q0 is cast only after its natural bound. The four substantive candidate proof bodies are `upper_rho0_six_power_gt_N`, `upper_rho0_q0_lt_six_power`, `actual_upper_rho0_stopped_q0_zero`, and `actual_upper_rho0_stopped_centre_eq_lower`.

The last two invoke the unmodified original event/PLUS-beta signed calculation at the literal power value of `w` and, when `N%4=0` and N is not prime, give exact equality of stopped centre correction with low-third centre. This is a specialized candidate theorem, **not** a claim that the actual high-level upper entry already instantiates `w` at this term. Verifying the entry and all changed lower/marked w parameters remains an internal open obligation. The result is not a full physical rho or H_N saving.

## Checks and limitations
Source-only file `P4AOriginalFull87Rho0SixCutoff.lean`: 98 lines. Static scan found zero `sorry/admit/native_decide/unsafe/axiom` escape tokens, but is NOT formal assurance. Exact rational check `6*(19/96)=19/16`; numerical smoke checks on N=8,12,16,100,1000,1000000 all satisfy the power inequality; none execute Lean or the real stopped event tree.

Commands in available runner:
- `lean --version`: exit 127, command not found.
- `lake --version`: exit 127, command not found.
- `elan --version`: exit 127, command not found.
- Total local RAM about 5.8 GiB; did not increase it.
- Frozen repository `lean-toolchain`, `lakefile.toml`, `lake-manifest.json` were inspected and match all three pins.

Verification: SOURCE_ONLY / UNEVALUATED / UNCOMPILED; no local elaboration, kernel replay, transitive axiom audit, saved87 replay or independent review. The source-only imports have not been staged to a complete pinned local Lake project. No CI, Codex, forced/merged push, or cloud resource expansion.

## Remaining obligations and concrete next action
First, inspect the actual upper producer entry to prove the symbolic `w` used at `sharedRankFour` is passed exactly `N^(19/96)` (or distinguish genuine parameter families where this is false). For other actual w, pay the full >=6-prime q0 signed occurrence invoice. Continue low-third centre, primitive and modulus-prime, fixed-theta same-rho PP, ordinary integral, actualParent/saved87, RAW eighth, unfiltered sixth BOTH, rank9/changed/tagged, three physical invoices and separate compiler/density reserves. Do not infer a global source or asymptotic theorem from a specialization. Compile/replay only with original frozen local toolchain if accessible.
