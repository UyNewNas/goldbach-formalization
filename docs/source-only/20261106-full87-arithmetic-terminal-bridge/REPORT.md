# P1.4 — actual full-q arithmetic terminal mismatch decomposition

**SOURCE_ONLY / UNEVALUATED / NOT COMPILED / ZERO FORMAL CREDIT. P1.4 remains YELLOW.**

## Exact recovery
- Previous verified task handoff: `d8ab731f88cb12bebed6457e4f68c920058774cb` on `chatgpt/p1-full87-signed-deletion-ledger-20261106`.
- Independent task branch: `chatgpt/p1-full87-arithmetic-terminal-bridge-20261106`.
- New candidate: `docs/source-only/20261106-full87-arithmetic-terminal-bridge/P4AOriginalFull87ArithmeticTerminalBridge.lean`, final source code commit `e70121813b21993bead44546333aec47f56dcaa5`; exact Git blob `5f077b2845da84b3dcaf5ff437577fc30437059f`; 419 lines.
- Manuscript PIN `UyNewNas/chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b`, `paper/source/manuscript-body.tex` blob `d529bea2ecfcc74d64fc1664ac770a3becaa7c79` (section 4).
- Unchanged fixed toolchain: Lean `leanprover/lean4:v4.33.0-rc1`, mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`, native `subfish-zhou/goldbach-lean@09b97db5764ade1246bfb77206baa1b124760958`. Constants `c=49044063/25000000`, `K=8452171/1250000`.

## Mathematical increment — genuine source rather than an invented signed coefficient

The original arithmetic source uses `signedTest R 1 (attachedLeafTest N cap 1 w L G)` for each genuine old/new eighth-state pair; the prior finite first-exit ledger uses `firstExitCorrection R halfProductDensity`. These are **not identical** without a terminal adjustment.

1. A recursion over the **original** retained select/skip tree identifies `signedTest R 1 selectedProduct` with `firstExitRetainedPolynomial R halfProductDensity`, starting from precisely `mass * ∏_{pre} g_N`. It does not reinterpret skip mass or remove occurrences.
2. The existing finite product-plus-correction identity gives, for the **same** incoming word, sign, mass, remaining carrier and two frozen policies, the exact old-minus-new decomposition:
   `ArithmeticOld - ArithmeticNew = (CorrectionOld - CorrectionNew) + (TerminalMismatchOld - TerminalMismatchNew)`.
   Here the actual sign-sensitive full-modulus terminal mismatch is `attachedLeafTest N cap 1 w L G positive word - ∏_{p∈word}halfProductDensity p`. The common Euler product cancels algebraically; the mismatch does **not** vanish.
3. Specialize to existing `ordinarySaving` (actual parent and finite cap), then the actual ordered `ownedSource` at every owner/trim cell, then the original full87 `physical_saving_eq_owned_sources`:
   `physical(sixth) - physical(eighth) = Σ_c ownedCorrectionGap(c) + Σ_c ownedTerminalMismatchGap(c)`.
   This is an exact original arithmetic coefficient identity, not a surrogate lower sieve bound, and retains the original source `G(mark*(a*pre.prod))`, beta attachment, selected words, signs and occurrences.
4. For each old/new leaf list, a separate absolute-value ledger bounds the exact missing full-q mismatch by the **sum of the absolute signed leaf values times their own terminal deviations**. A proved list induction gives the corresponding owner-state bound. No uniform/asymptotic estimate for this cost is claimed.

## What was actually eliminated
- The prior conflation risk between physical g_N failed-event correction and unit-weight full-q arithmetic `signedTest`: their **exact difference** is now exposed in a candidate derivation and explicit genuine terminal cost. This does **not** prove numerical error smallness or a saving.
- The previous rank>=11 deletion-factor comparison is still only a **one-time finite comparison ledger**. It has not been substituted for original arithmetic density, and must not be paid twice.

## Checks and boundaries
- GitHub created the source-only commits and source readback matched blob `5f077b2845da84b3dcaf5ff437577fc30437059f`, 419 lines; static scan of code outside comments found no `sorry/admit/axiom/native_decide/unsafe`; bracket/delimiter count balanced.
- Independently tested the precise recursive algebra with exact Python `Fraction`: 14,000 deterministic random signed policy/terminal/weight cases, 0 mismatches for retained polynomial, old-minus-new cancellation and the two-leaf-tree absolute cost. Synthetic domains only, NOT real saved87 source/archive.
- Fixed Lean/Lake compiler not present in this runtime; **NOT RUN**: typechecking, kernel replay, transitive axioms, independent review, actual archive replay, CI. `SOURCE_ONLY=true, UNEVALUATED=true, COMPILED=false, KERNEL_REPLAYED=false, TRANSITIVE_AXIOMS=false, INDEPENDENT_REVIEW=false`.

## Exact internal gaps
- Prove original arithmetic terminal deviation bounded sharply enough, **using the same actual physical AP/coprime/centre/modulus source**, not an arbitrary separate sieve bound. The finite literal absolute ledger is not yet a quantitative reserve payment.
- Bridge the difference of **both** old/new first-exit correction series with later-event and rank-nine contributions: existing later ledger is rank>=11 and one comparison factor only. The rank-nine inherited-square loss is still unpaid. No claim `adjustedFailedValue = attachedLeafTest`.
- Complete actual `RealizedHistory` on every owned state, primitive/centre/modulus discrepancy, original sixth filtering, saved87 archived gains, ordinary residual-integral asymptotic, changed/tagged, independent compiler+density reserves and same rho assembly. Keep all `SOURCE_ONLY` chains unaccepted pending matching frozen Lean compilation.

**Next precise action:** isolate the physical `correctionGapAt` as the difference of the *same two* actual failed-attempt lists (parent versus finiteCap, both on same state) and split its ranks 9 / >=11 without changing signs or occurrence order. Only then attach the already-once-paid deletion ledger and explicitly keep the `ownedTerminalMismatchCost` AP/centre/modulus obligation. No external proof expansion.
