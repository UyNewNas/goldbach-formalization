# Persistent P1.4 handoff — actual original87 signed centre-prime fibres

## Reliable recovery
New task branch: `chatgpt/p1-full87-centre-fibre-20261111`.
Source of this continuation: `chatgpt/p1-full87-signed-sharp-recenter-20261111` at *verified* `1e01d9c7fee860a0cbed598ee2862058d103c163`. Source patch commit `4f4fb3f33aa3c168ecf61a6ac003c23042490c6a`; audit patch commit `c1cf735764d146dd8e22fac6d86f7e6ea9498d8a`; documents follow. Read the LIVE branch ref and latest REPORT, REGISTRY, INPUT_BOUNDARY and COMPLETE Lean source before continuing. Do not reset to stale 9649ab3. Other P1/P3/P5/CI branches are unrelated and untouched.

Proof packet: `docs/source-only/20261111-full87-centre-fibre/`.
- `P4AOriginalFull87CentrePrimeFibres.lean`, verified Git blob `fdb559d272d0c5e0f604516f5865b36dd40e81bb`.
- `check_finite.py`, verified Git blob `e622211f2f510b585e167442c8c1b8d1c0879295`.
- REPORT, INPUT_BOUNDARY, REGISTRY and this HANDOFF are at the same path; use live blob checks to detect concurrent changes.

## Provenance
Frozen manuscript UyNewNas/chen-imbalanced-semiprimes@`9731290e8f53cffda44129906cde6a965eaa869b`, `paper/source/manuscript-body.tex` blob `d529bea2ecfcc74d64fc1664ac770a3becaa7c79`. §4 `eq:current-PP`, `lem:current-sharp-prime` / `eq:current-sharp-pi` genuinely checked at the pin. Lean v4.33.0-rc1 / mathlib e4c91783ca8e6a7c693ae624ade32fd22d4e43c1 / native 09b97db5764ade1246bfb77206baa1b124760958. c=49044063/25000000, K=8452171/1250000. No pins changed.

## Actual new mathematics
The earlier sharp recentering cancels only the *modulus-prime* term. The centre-prime correction survives. This packet's candidate Lean proof expands the centre correction as a genuine finite set of original prime divisors P|N and congruence fibres P≡N mod *the complete original modulus d*; switches the signed physical old-minus-new rho sum with that P-fibre; ties it back to the actual 87 owned occurrence list via `gain_eq_owned_sources`; and derives
`|gain(centrePrimeAP)| <= sum_(P|N prime<=N) sum_(d in actual old/new full support; P≡N mod d) |rhoSixth(d)-rhoEighth(d)|` (with each coefficient zero-extended off its own support).
Under `¬Nat.Prime N`, centre divisor P<N and every congruence incidence has `d|N-P` and `N-P>0`. Boundary `d=0` or `d=1` is not silently discarded in the finite identity.

The two *separate* original sixth/eighth signed sharp PP hypotheses remain unproved. The conditional receiver bound is their two errors plus this actual centre-prime fibre budget, with NO second modulus-prime charge. NO numerical o(H_N) or reserve claim.

## What was actually checked
The local fixed Lean/Lake/Elan commands were absent (version check exit 127); no fixed mathlib/native closure. Static syntax/banned-escape checks completed, but there was NO Lean elaboration. Finite Python test `check_finite.py` successfully ran: 10,506 (N,d) centre count comparisons including d=0, plus 5,000 synthetic overlapping signed physical old/new coefficient cases and their absolute budgets, zero failures. A corrected Python generator test was rerun successfully; it is not an original87 source or saved numerical witness replay. SOURCE_ONLY / UNEVALUATED / UNCOMPILED; no kernel replay, transitive axiom checks, independent review. Never promote source-only to compiled on the basis of these finite tests.

§4 PP / sharp endpoint remain REGISTERED_NOT_PROVED / NOT_CALLED. No CI, Codex, external foundations, user-local host, main/master, merge, force push or resource increase.

## Specific next step
1. Check actual support and total coefficient size for the original sixth/eighth full moduli and try to *prove* an upper bound for the literal `centreFibreAbsBudget` on the SAME `H_N` scale (including exact P|N and d|N-P incidences). Do not silently estimate an unrelated sieve bound or pretend a finite invoice was paid. Avoid duplicating the already cancelled modulus term.
2. Independently establish actual sharp PP class admission for BOTH original physical policies (fixed parameter, squarefree, coprime (d,N), bounded full modulus, signed beta, smooth singleton/trim/legal X). Any genuinely external theorem stays registered, not implemented.
3. Continue ordinary continuation→same residual integral; weighted actualParent gap; archived saved87 witness; low/high q, raw/finite/filtered, rank9, changed/tagged, distinct two reserves and final same rho.
4. If exact pinned Lean environment becomes available, adapt source-only import paths and typecheck smallest closure. Correct actual elaboration errors before expanding candidate scope.

P1.4 remains YELLOW.
