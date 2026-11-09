# P1.4 — literal low-q complete-modulus PP: a finite source-mass envelope

## Recovery and exact versions
Predecessor: `e73486e24e44c36170783903ef5c2e102db00418` on `chatgpt/p1-full87-pp-cutoff-lowq-invoice-20261109`. Read actual predecessor REPORT.md, HANDOFF.md, REGISTRY.json, INPUT_BOUNDARY.md and complete 212-line source, plus the physical rho source, real small/rough support, signed continuation, actual prime source, and the fixed manuscript §4. No AGENTS.md was found at the repository root, docs or docs/source-only. The latest *source* increment on this independent task branch is `a7652157f8af32631522193f5c293690db86f63a` ([skip ci]); this metadata commit is later. Do not reset to navigation baseline 9649ab3.

Frozen paper pin: `UyNewNas/chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b`, `paper/source/manuscript-body.tex`, blob `d529bea2ecfcc74d64fc1664ac770a3becaa7c79`. Same c = 49044063/25000000, K = 8452171/1250000. The unchanged Lean toolchain is v4.33.0-rc1 / mathlib e4c91783ca8e6a7c693ae624ade32fd22d4e43c1 / native 09b97db5764ade1246bfb77206baa1b124760958.

New source: `docs/source-only/20261109-full87-lowq-absolute-envelope/P4AOriginalFull87LowQAbsoluteEnvelope.lean`, Git blob `3649985891a1beba88c89d2ce0c0840e489f744f`, 197 LF-separated segments (196 complete lines plus trailing newline), two public candidate theorem bodies and three private supporting proofs. The predecessor's exact high/low split and true q-coprime PP mean are unchanged.

## Actual mathematical increment
Let R and S denote the original RAW sixth-dispatch and LICENSED fifth/sixth/eighth policies. Their complete supported physical rho and original full modulus support M are reused WITHOUT constructing a surrogate policy or dropping any signed small Rosser or rough occurrence.

Set Q_low(X)={d in M : d <= X}, Δrho(d)=rho_R(d)-rho_S(d), E_W(d)=finitePrimitiveDiscrepancy(chenPrimePrefix(N+D),W,N,d), and T_W=Σ_(p in chenPrimePrefix(N+D)) |W(p)|.

1. For any positive physical modulus d coprime to N, the existing *finite reduced-residue recentering* lemma implies |E_W(d)| <= 2 T_W, using the original prime prefix and arbitrary signed W. This is derived from the literal congruence source and no asymptotic or PP input.
2. From the project's literal `actualSmallRoughRho_abs_le_one`, each actual R/S `supportedPhysicalRho` is one-bounded, even off its own support. Consequently |Δrho(d)| <= 2 pointwise.
3. The new candidate derives the non-asymptotic literal low-q bound
   |Σ_(d in Q_low(X)) Δrho(d) E_W(d)|
     <= 2 T_W Σ_(d in Q_low(X)) |Δrho(d)|
     <= 4 |Q_low(X)| T_W.
   No extra equality-case exemption, cancellation claim, N-independent mask, or signed monotonicity is used. The strict boundary d=X remains in Q_low.

This *replaces an unbounded literal error factor with explicit finite source mass and real coefficient variation*, but the resulting bound can be far too large to be o(H_N). It is a conservative fallback, NOT a completed payment of the low-q term or an independent PP distribution estimate. Its usefulness now depends on proving a sharp bound for the ACTUAL coefficient variation/cardinality relative to H_N, or separately licensing a filtered PP theorem.

## Actual checks and evidence limitations
- GitHub created source commit `a7652157f8af32631522193f5c293690db86f63a` and fetched back the complete `P4AOriginalFull87LowQAbsoluteEnvelope.lean` at its task branch. Git blob agreed with `3649985891a1beba88c89d2ce0c0840e489f744f`. No forbidden proof escape token, source retains 3 imports and 2 public / 3 private theorem bodies.
- Independent exact Python Fraction synthetic tests: 2,000 trials, 1,419 q-label appearances common to both generated policy supports, random signed weights, random signed coefficients each bounded by 1, positive target-coprime moduli, arbitrary integer X, zero counterexamples to both invoices and the primitive bound. **Synthetic only; original full87 saved geometry and actual coefficients were not numerically evaluated.**
- Local `lean --version`, `lake --version`, `elan --version`: all exit 127 (command not found). No matching pinned build artifacts available; no Lean/Lake elaboration, kernel replay, transitive axiom audit or independent review. This file remains SOURCE_ONLY / UNEVALUATED / UNCOMPILED, not COMPILED or kernel-certified. No CI dispatch, Codex call, main edit, toolchain update or extra cloud resources.
- Typechecking requires staging source-only imports in the pinned project import closure. A static scan, Fraction regression and Git SHA are not typechecking.

## Exact remaining work
1. Prove a meaningful N-dependent upper bound for the original low-q coefficient variation `Σ_(d<=X)|Δrho(d)|` or establish an actually authorized filtered PP bound, then pay it relative to the SAME H_N. Current factor `T_W` may be of order N/log N, so the present cardinal bound alone is not acceptable as o(H_N).
2. Authenticate original W_N and original complete-product Gevrey/chart support, the legal manuscript PP integer X, physical q exponent, and both genuine policies' PP permissions. The external §4 PP theorem is REGISTERED_NOT_PROVED / NOT_CALLED.
3. Authenticate original 87 saved geometric witnesses, N-dependent actual parent/common ancestry, actual source membership and signed ordinary/residual gain.
4. Pay high-q stopped/five-frontier plus endpoints/centre and raw/finite/filtered losses, rank9/changed/tagged and the two independent compiler/density reserves.
5. Compile against exact Lean/mathlib/native pins when present, fix elaboration errors, and independently audit kernel/axiom dependencies. P1.4 remains YELLOW.

NEXT CONCRETE ACTION: inspect real fifth/sixth first-disagreement support to bound `Σ_(d∈Q_low) |Δrho(d)|` using unchanged actual signed carrier and small-Rosser factorization, not `4 |Q_low| T_W` as a claimed asymptotic payment.
