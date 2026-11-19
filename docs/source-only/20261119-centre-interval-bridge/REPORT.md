# P1.4: source-exact primitive interval and centre-prime split

Baseline `5f47e51e999e03b73518132b3e357d4b8b593d0f`, source commit `f404383000d6ab422861877a9ead1e4cab3cdc21`, source blob `37cd9b965279f34295c9cb8f0635a67ae972c4b5`. Independent branch `chatgpt/p1-full87-centre-interval-bridge-20261119-2110`. New proof candidate: `P4AOriginalFull87CentreIntervalBridge.lean` (222 lines).

## Manuscript-internal advance

The original FULL-modulus anchored discrepancy at strict quotient gate ell is a reflected interval discrepancy:
`Q_b(k)-Q_b(ell) = sum_(ell<=a<k) [1_{N-ab in chenPrimePrefix N} - mean(b)]`.

Using the **actual** `chenAdditivePrimeCarrier_eq_prefix_filter` (not a surrogate source), this equals
`sum_(ell<=a<k) [1_{N-ab in chenAdditivePrimeCarrier N} - mean(b)] + sum_(ell<=a<k) 1_{N-ab prime AND (N-ab)|N}`.
The centre term is literal, nonnegative, and is NOT automatically zero. The original PLUS-beta weight vanishes for a<ell, hence every true weight jump t has ell<=t+1. For 0<b=(p::pre).prod and k<=N/b+1, every reflected integer on this quotient interval belongs to the original residue class N mod b, preserving strict bounds. None of these operations changes the original parent, fifth/sixth List occurrence, beta coefficient, or source.

Combining with the existing anchored Abel proof gives a **conditional** original weighted-prime error bound `(E+C)*originalRoomBetaVariation`, where E bounds the actual additive carrier interval error at true beta jumps and C bounds its centre-divisor count at the SAME endpoints. This is a single correction payment; neither bound is yet established in the actual producer.

IMPORTANT counterexample to erroneous global centre cancellation: N=70,b=13,a=5 gives N-ab=5, prime dividing N, gcd(13,70)=1, original ell=3 (X=0) and m=6. Thus centre primes may occur in an unweighted interval even when the true PLUS-beta **support-restricted** upper fibre excludes them. This is a generic finite witness, NOT an actual six-factor occurrence certification.

## Performed checks

GitHub re-read verified source blob `37cd9b965279f34295c9cb8f0635a67ae972c4b5` and exact source commit. Static banned-escape scan: none. Finite seeded diagnostic: 30,000 cases, 415,093 quotient positions, 46,877 actual beta jumps, zero failures for lower gate and carrier/centre interval identity. Not Lean evaluation or producer estimates.

Current container: `lean --version`, `lake --version`, `elan --version` unavailable (exit 127); cgroup memory.max 4294967296 bytes. **SOURCE_ONLY / UNEVALUATED / UNCOMPILED**. No kernel replay, axiom audit, independent review, CI, Codex, upgraded pin, main/master change or added cloud capacity. Applicable AGENTS.md not found at repository root/docs/docs/source-only.

Frozen Lean `leanprover/lean4:v4.33.0-rc1`, mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`, native `09b97db5764ade1246bfb77206baa1b124760958`. Manuscript commit `9731290e8f53cffda44129906cde6a965eaa869b`, body blob `d529bea2ecfcc74d64fc1664ac770a3becaa7c79` verified. c=49044063/25000000 and K=8452171/1250000 unchanged.

## Remaining manuscript-internal obligations

Stage the source-only ancestral imports at fixed pins, compile and repair elaboration errors. Authenticate an actual same-rho primitive reflected AP interval input at all true beta jump endpoints; prove correct N-uniform quantifiers, source and normalization. Bound the centre-prime C and original beta variation plus ordered fifth/sixth occurrence budget relative to H_N without repeated lower/reserve payment. Finish lower-half primitive/modulus-prime/centre, ordinary residual integral, saved87, RAW/BOTH/rank9, changed/tagged and two independent compiler/density reserves. P1.4 remains YELLOW.
