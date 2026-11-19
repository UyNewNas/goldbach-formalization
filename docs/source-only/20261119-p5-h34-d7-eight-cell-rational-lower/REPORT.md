# P5.6 → h34 | original D7 second-affine eight-cell rational certificate

Date: 2026-11-19. Baseline: `c2e5d463233b152e1b632fa46040b91ab2bc8295`.
Branch: `chatgpt/p5-h34-full-tagged-actual-fin-20261112`.
Frozen manuscript: `UyNewNas/chen-imbalanced-semiprimes@ba6ec11d`.
Status: SOURCE_ONLY / UNCOMPILED / UNEVALUATED / FULL_H34_OPEN.

## Actual manuscript-internal increment

New `Part5OriginalH430D7EightCellRationalLower.lean` contains a *generic genuine* second-affine D7 cell-soundness proof candidate: the moving `max u (1-16u/5)` endpoint is handled by the existing `lowerEndpoint_second` source, and the second-piece real logarithm argument is shown decreasing. The positive rational 2-term logarithmic series and increasing denominator `u*(1-u)` give a right-endpoint Darboux lower bound on every literal cell. The `q=1` case at the upper support endpoint is treated without an assumed positive tail.

Literal second-piece partition:
`[5/21,49/200,1/4,51/200,13/50,53/200,27/100,11/40,100/353]`.
Exact rational argument floors at successive *right* endpoints:
`40000/31997,800/659,1960000/1662447,40000/34931,1880000/1690223,460000/425763,8000/7623,1`.

Independent Python Fraction diagnostics: all eight q equal the original rational logarithm argument at the specified right endpoints; all q>=1; the exact sum of the eight 2-term Darboux masses is approximately `0.027262225654410867`, strictly greater than `27/1000` by `0.0002622256544108661`. This diagnostic is **not** a Lean certification or a real-integral proof.

Lean candidate `genuine_d7_eight_cell_ge_27_per_1000` pays all eight cells using actual interval-integral additivity and separately includes the entire original first D7 affine piece as nonnegative. Thus no slice, moving support gate, or junction is silently discarded.

The new seven-term consumer `actual_lambda_ge_398_over_5000` uses previous genuine candidates:
three singleton floors `57/1000 + 1/200 + 29/1000`; D5 `13/100`; D6 `11/100`; new D7 `27/1000`; D8 `1/25`, divided by original five exactly once. The candidate lower bound is `0.0796` (previous candidate `0.0758`). It does **not** imply `lambda>=0.13`.

## Evidence and scope limits

The runtime has no Lean/Lake/Elan binary or installed staged closure (frozen repo toolchain `leanprover/lean4:v4.33.0-rc1`). Native GitHub DNS failed; connector-driven Git object operations were used. This source is staged under docs/source-only, not installed as `ImbalancedChen/` production import. No Lean/Lake compile, kernel replay, transitive axiom audit, CI test or finite Lean certification was executed. Python exact rational equality, blob consistency and text checks are NOT Lean success.

No modifications to P1.4/P3.6, target, frozen manuscript, c/K, root norm7/2, row norm12, alpha, same-Q, original 106 bank, 430+11 or CI/dependencies. No new external analytic input, custom axiom, sorry, admit, unsafe or native proof escape.

## Still open (manuscript-internal)

1. Full original seven-source strict >=0.65 numerical certificate, presently only partial candidate lambda>=0.0796; all source-only ancestors still require Lean compilation.
2. Frozen fixed `20249/1000000` real count intercept; actual frozen F initial seed and both CLOSED-CELL tables.
3. Actual all-action 430-step retention/Buchstab/bank quantitative induction.
4. Complete original U3/U4 selected counts, root weights, owner, inherited/selected/full filters and rejection payments.
5. PP/same-rho instantiation; native-history mass and integral–Theta–count; one common nested 430+11 causal refinement.
6. Complete staged import closure, local Lean/Lake build, kernel replay, transitive axiom review and finite certificate evaluation.

Next: stage and compile this new D7 module **with its pinned source-only imports** when the toolchain/closure is available; repair actual elaboration errors; then target a comparable full-support D8 or singleton rational certificate rather than repeatedly refining this already-positive D7 source.
