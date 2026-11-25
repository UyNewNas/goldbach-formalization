# Directed logarithm recursion diagnosis and candidate — 2026-11-25

## Status

**The new source candidate is UNCOMPILED and has no new kernel or declaration-audit receipt.** This review read the actual prior CI job logs, source manifests, frozen manuscript, and the pinned Lean implementation. No compiler, numerical producer, native decision procedure, or CI submission was run by the reviewer. The coordinating agent owns compilation and the unchanged complete declaration audit.

Only `ImbalancedChen/P2DirectedLogRounding.lean` was changed. No audit rule, import, original arithmetic definition, original theorem statement, certificate data, or concrete-run parameter was changed.

## Exact prior evidence

The comparison baseline is `UyNewNas/goldbach-formalization` commit `2dbe821e7f6eabc4fd7ec4de793d4e243c1df02b`. Its target file is byte-identical to the v3 file staged by the first run below.

| Evidence | Observed result |
| --- | --- |
| [Run 44468647712](https://github.com/UyNewNas/goldbach-formalization/actions/runs/44468647712), workflow commit `a4efaf41df98d00c1bf216d6d80086b96a517d39`, job `135372458979` | Step 11 compiled all three local-closure modules successfully. Step 12 replayed all three with the bundled kernel checker successfully. Step 13 failed at `CandidateAudit.lean:14:0`: `Partial declaration in a P0 batch module: ImbalancedChen.Certificates.P2DirectedLogRounding.Expr.Valid._unsafe_rec`. |
| [Run 44477066566](https://github.com/UyNewNas/goldbach-formalization/actions/runs/44477066566), workflow commit `37458a4ac2b8b3785766c62cd2f375740a8be7f0`, job `135400067789` | The subsequent explicit `Expr.rec` overlay failed in the target module during step 11. Lines 195:17, 232:4, and 276:4 reported that the code generator does not support `Expr.rec`. Line 222:9 reported the resulting noncomputable `instReprExpr.repr` dependency. Kernel replay and declaration audit were skipped. |

Both runs staged the same frozen source commit, `b7b0f5613f1b34855e0da7ad44d1d79ed34519cf`, through `verification/parts/p0/p2-directed-api/stage_candidate.py`. Their respective manifest SHA-256 values were `da9eaf4f13e313b00eb8c19f09cc1c32bcb9041680cf41d8a19dd6d2997b3e8c` and `a79b0338db425110e855e195e89c9123ea8ce4aadf8a74e044e4b13b68d0b406`.

The first run installed `docs/source-only/20261110-yellow-closure-10t/t01_remote_fifth_kernel/v3repairs/P2DirectedLogRounding.lean`, with no overlay. Its target SHA-256 was `11d018492ac313d814c9a18df0624e65275571b4c7725d9486ca57c00f3fbcd3`. The current baseline file and its v3 source copy both have that hash. The local direct dependencies also match that run exactly:

| Module | SHA-256 |
| --- | --- |
| `ImbalancedChen.Certificates.RationalLogCertificate` | `4d705f561d4ba07e01dd7b3af1b0a73bcbf28c9dd6d2ddfd4ae288fb84de9d22` |
| `ImbalancedChen.Certificates.PairedFibreIntegral` | `d8bcdab8e5010d16827f5074db713243adc6a1cd686ab2b69bd3f9b4e41039a4` |

The second run's overlay was `verification/parts/p0/p2-directed-api/P2DirectedLogRounding.lean`, SHA-256 `1e9248b316da9173ca8afd970dce5f79d9f3dee4818b7791b540b2fc14dcf082`. That failed overlay was not installed. The current baseline already contains the earlier, successfully compiled API repair: both rounding-error proofs use `mul_lt_mul_iff_left₀` in place of the old `mul_lt_mul_right` invocation.

These failures do **not** show a gap in the logarithm, four-corner, floor/ceiling, or paired-integral mathematics. The first is a stricter serialized-declaration requirement; the second is a code-generation failure introduced by an attempted remedy.

## Why the original audit fails

The first job's complete serialized inventory contains four generated companions:

- `Expr.Valid._unsafe_rec`
- `Expr.check._unsafe_rec`
- `Expr.enclosure._unsafe_rec`
- `instReprExpr.repr._unsafe_rec`

All names have prefix `ImbalancedChen.Certificates.P2DirectedLogRounding.`. The audit stops at the first one in its sorted scan. Fixing only `Expr.Valid` would leave the other three inventoried companions.

This behavior is explained by the pinned `leanprover/lean4:v4.33.0-rc1` implementation. [`Structural/Main.lean`](https://github.com/leanprover/lean4/blob/v4.33.0-rc1/src/Lean/Elab/PreDefinition/Structural/Main.lean) calls `addAndCompilePartialRec` after elaborating the total logical definition. [`PreDefinition/Basic.lean`](https://github.com/leanprover/lean4/blob/v4.33.0-rc1/src/Lean/Elab/PreDefinition/Basic.lean), `addAndCompilePartialRec`, creates a generated companion with `DefinitionSafety.partial` when code generation is requested. Adding `termination_by structural` alone would not remove that mechanism.

The public logical recursion and its compiled companion are distinct declarations. Prior kernel replay succeeded, but the unchanged project audit rejects any owned serialized declaration marked unsafe, partial, or axiom. This candidate addresses that declared acceptance condition directly; it does not omit generated declarations from the census or relax the audit.

## Candidate repair

| Version | Target SHA-256 |
| --- | --- |
| Original at `2dbe821e7f6eabc4fd7ec4de793d4e243c1df02b` | `11d018492ac313d814c9a18df0624e65275571b4c7725d9486ca57c00f3fbcd3` |
| New uncompiled candidate | `9dbfd25cc94f8aae9fbb163bda717c84845d3b04296193211ed902a39cccceb0` |

`Expr.enclosure`, `Expr.check`, and the same six-constructor `Repr` traversal now use an explicit `WellFounded.fix` over `measure sizeOf`. Each recursive child is proved strictly smaller. The definitions do not recursively refer to themselves; recursion is supplied by the standard-library fixpoint. The project's existing `P2OriginalPrioritySerialQueue.popBest` and tree aggregation code use this same form. The pinned [`Init/WFComputable.lean`](https://github.com/leanprover/lean4/blob/v4.33.0-rc1/src/Init/WFComputable.lean) supplies the compiler equations for `WellFounded.fix`.

`Expr.Valid` is marked `noncomputable`: it is a proposition-valued description used by proofs, while the Boolean checker remains executable. Its body, its six logical cases, and the permitted certificate premises are unchanged. The already noncomputable real evaluator is unchanged.

Twelve constructor equations expose the original six cases for each of `Expr.enclosure` and `Expr.check`. The existing induction proofs use those equations. This preserves the data functions extensionally and supplies explicit rewrite rules; it does not claim that the old and new recursive definitions are definitionally equal on open terms. The renderer retains the original constructor names, argument order, and application-parenthesis format. No logarithm evaluator, tail estimate, rounding rule, or integral identity was replaced.

Static inspection confirmed that all **22 original theorem statements** remain unchanged after whitespace normalization; only the 12 constructor equations are added. `git diff --check` passed. This is source-level evidence, not a successful Lean check. Compilation, kernel replay, and the full regenerated serialized inventory must all be checked before accepting the candidate.

## Frozen manuscript correspondence and scope

The manuscript remains `UyNewNas/chen-imbalanced-semiprimes` at `3ffa2d159c9974e2ca6d5f930c0f2c16baa0135e`:

- [`paper/release-20261106/en/numerical-appendix.tex`](https://github.com/UyNewNas/chen-imbalanced-semiprimes/blob/3ffa2d159c9974e2ca6d5f930c0f2c16baa0135e/paper/release-20261106/en/numerical-appendix.tex), Directed arithmetic, lines 94–120, gives outward floor/ceiling endpoints, all four products, and the positive odd logarithm series with explicit tail (`num:log-enclosure`). The manuscript also describes the separate higher-precision paired calculation. None of those precision settings is adopted as a replacement for the original compact run here.
- [`verification/data/certify_conservative_chen.py`](https://github.com/UyNewNas/chen-imbalanced-semiprimes/blob/3ffa2d159c9974e2ca6d5f930c0f2c16baa0135e/verification/data/certify_conservative_chen.py), SHA-256 `67b9429667e18786058e0fe58676fbe09d556868468f1281166cac2b55f8604e`, fixes `BITS = 80`, `LOG_TERMS = 32`; `I.__mul__` encloses four products; `atanh_log_bounds` rounds every recurrence outward and retains the geometric tail divided by `2 * LOG_TERMS + 1`; `log_point` retains the sign-dependent range-reduction interval endpoints.

The changed module supplies a generic signed enclosure API, not a claim that its `RationalLogCertificate` fields equal a historical log32 output. Its existing imported certificate theorem uses Mathlib's more conservative remainder without the additional `2n+1` denominator. That pre-existing scope is unchanged. The separate historical log-point/interpreter chain supplies the original log32 binding used by the compact run.

The unchanged `Enclosure.mul_contains`, `roundDown_error`, `roundUp_error`, `Enclosure.round_contains`, and `Expr.check_sound` retain the signed four-corner and directed-rounding meaning. `pairedLocalIntegral_directed_bounds` retains the literal `K / 80`, the exact log-argument equalities, and the original geometric positivity assumptions. It gains no new endpoint premise.

This source candidate supplies no evaluation of the original two-million-split guard and no new whole-functional endpoint. The original compact acceptance boundary remains the separately reviewed complete forest and supported `681/100` endpoint in `semantic-review.md`.
