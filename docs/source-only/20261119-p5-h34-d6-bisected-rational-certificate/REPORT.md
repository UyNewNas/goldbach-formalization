# P5.6 h34 — actual D6 bisected rational certificate

Date: 2026-11-19 (Asia/Shanghai).
Incoming branch HEAD: `31af16a1a6c63d805c583c740312589937ea3a2f`.
Branch: `chatgpt/p5-h34-full-tagged-actual-fin-20261112`.
Fixed manuscript: `UyNewNas/chen-imbalanced-semiprimes@ba6ec11d800eccc54406490631895e174de85766`.
Fixed toolchain: Lean `leanprover/lean4:v4.33.0-rc1`; mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`.

**PARTIAL_SOURCE_INCREMENT / SOURCE_ONLY / UNCOMPILED / UNEVALUATED / FULL_H34_OPEN.**

## Actual manuscript-internal source delta

`Part5OriginalH430ActualD6BisectedRational.lean` consumes the previous true D6 cell-integral soundness lemma at the **two adjacent rational subintervals** of the unaltered physical outer interval `[50/227,100/353]`. Midpoint `20175/80131` is the exact rational average, not a new domain cutoff. The new generic `d6_two_cell_integral_lower` proves additivity via the real interval integral and continuous original logarithmic outer slice.

Two calls to the original two-term `logSeriesLower` and an exact rational arithmetic check yield the strictly stronger candidate `d6Log >= 11/100` (previous packet `>= 103/1000`). Independent exact rational arithmetic gives two-cell sum approximately `0.1100301554036517` with a positive gap of approximately `3.01554e-5`; only the rational expression is passed to `norm_num`, not the float.

The original seven-term normalization then gives `lambda >= 11/500 = 0.022`, and `actualFeedback (1/50) >= 11/25000`. These are **partial** bounds, not the required `lambda >= 13/100`. The unchanged D5/D6/D7/D8 supports and singleton integrals are not replaced by surrogate coefficients.

## Honest boundary

No claim that the fixed analytic `20249/1000000` contribution has been paid. No inference that frozen analytic F dominates the full Q80 seed. No full 430-generation CLOSED-CELL proof, U3/U4 owner/count, PP/same-rho, native-history, integral–Theta–count or common 430+11 causality proof.

Native `git ls-remote` fails `Could not resolve host: github.com`; `lean`, `lake`, `elan` are not on PATH, and no installed fixed import closure is present. Authenticated GitHub connector permits source-only write/remote SHA checks, **not** a local compiler run. No CI configuration, toolchain or other proof branch touched. Lean elaboration, kernel replay, transitive axiom audit, and finite certified guards remain **UNEVALUATED**, not COMPILED. The source proof is a candidate.

## Next step

Compile this source plus its fixed import closure once available; repair actual errors. Continue real multi-cell rational Darboux bounds for the other six original integrals and sharpen total to 0.65, separately trace and prove the analytic fixed-intercept and actual frozen F seed inequality. Do not add target-equivalent hypotheses or externalise manuscript-local obligations.
