# P2 strict04: Ledger and original Q80 table proof-expression repairs

## Actual input and failure evidence

- Original strict checker task: `1cd8f8cb588f4df1a9a9007c22fe7314`.
- Compiled source: `f5d007b8fd4c3a288ca23444c6d8a4e7f6bd8a07`.
- Local baseline: `b52331f1c6cc5c38e9ed331b8b7c738c5dd94b45`; both assigned Lean files were byte-identical to the compiled source before this repair.
- Complete log: `docs/source-only/20261125-p24-original-compact/p2-strict-symbolic-04.log`, 20,768 bytes, SHA-256 `9e2e3ff4e18c6f1b2ee5f7e1efba1210a767aae9fe66b423913e65dbc7751096`.
- Parent-observed completed task: 193.667 seconds, peak 6.98 GB, 276/319 successful modules (267 reused, 9 fresh). The log explicitly reports `PASS ImbalancedChen.P2HistoricSieveStateInduction`.
- Ledger now reports only the line 570 `castAsMap` rewrite mismatch. Its earlier memory and typing errors do not recur in this complete run; Ledger itself remains failed pending this repair's verification.

## Manuscript boundary and classification

Rechecked the frozen 1106 sources at publication commit `3ffa2d159c9974e2ca6d5f930c0f2c16baa0135e`: `paper/release-20261106/en/numerical-appendix.tex`, directed arithmetic and delayed-function enclosure paragraphs (lines 94–143), and `verification/data/certify_extended_prefix.py`, `SieveTable`/`numerator`/`point` (lines 51–113) and complete-ledger versus heap updates (lines 402–437). Local cached copies are under `/workspace/scratch/daaa8ebc2a3f/p24-ci-audit/frozen-1106/`.

All reported sites are expression/API or redundant-tactic failures. The interpolation equality uses the existing hypothesis `hb : 0 < b` to derive the nonzero real denominator; it introduces no premise or mathematical result beyond the already passed StateInduction proof. The original Q80 table, maximum 12, divmod query, interpolation bounds, all terminal charges and their ordering remain unchanged. No omitted analytic derivation or substantive manuscript gap is implicated by these failures.

## Minimal candidate

| File and original error site | Change |
| --- | --- |
| `P2OriginalPriorityForestLedger.lean:570` | Replace the local `castAsMap` statement's `show List ℝ from do ...` with `((do ...) : List ℝ)`. The actual error shows the former elaborating to a `have this := ...; this` wrapper while the target contains a bare `do`. Keep the existing flatMap proof and consumer rewrite unchanged. |
| `P2OriginalCompactQ80Table.lean:42,52` | Add `Nat.cast_ofNat` to the two exact `simpa only` lists, as in the passed StateInduction query/index proofs. |
| `P2OriginalCompactQ80Table.lean:101` | Reuse the passed StateInduction `hchord` proof verbatim: derive `(b : ℝ) ≠ 0` from `hb`, rewrite `Int.cast_sub`, `sub_div` and `div_self`, then use `hwForm`. This includes the passed sequential `push_cast; ring` form within the same chord proof. |
| `P2OriginalCompactQ80Table.lean:165` | Remove the actually reported redundant `ring` after `field_simp [hqpos]`, matching the passed StateInduction `hactual` proof exactly. |

## Byte and interface checks

| File | Before SHA-256 | Candidate SHA-256 |
| --- | --- | --- |
| `ImbalancedChen/P2OriginalPriorityForestLedger.lean` | `54692ecb6f7fc9926b14291720586033ac8a49f43755600bb4f08300f6c7cbe7` | `eaa2da888add0b1790c829e43dad138b2bed8721500fdf97fe42eb95863a1af1` |
| `ImbalancedChen/P2OriginalCompactQ80Table.lean` | `e9f37ac098bb46dc8befa0211d7c39ac8a0907ef675b9ebca824ffa58d49e66a` | `04109765062cbd99e2e23555e2ca4f4ab1d0e1b69a2a346e9d4ea4a7bd766e84` |

Mechanical comparison against the local baseline preserves all 32 existing Ledger theorem headers, its 20 complete computational declaration blocks and both imports; all four Q80Table theorem headers and its sole import are unchanged (the file has no standalone computational declarations). No new declarations or imports were added. The Q80Table `hchord` and `hactual` blocks are byte-identical to the corresponding blocks in the now-passed StateInduction source. Original line-ending bytes outside the replacements are preserved. Scoped `git diff --check` passes; no forbidden proof escape, linter disabling or resource option is added.

Independent read-only review by `p24_project_cache_reuse` of both candidate hashes found no static blocker. It independently checked the bare-do type annotation, the cast normalization, the denominator argument, unchanged theorem headers/imports, and the exact correspondence of both Q80 proof blocks with the passed StateInduction blocks. This review did not edit files or invoke a compiler.

Only these two Lean files and this new note were edited. No index, commit, ref, remote source, P2 environment or compilation was touched. Candidate acceptance remains pending the parent's unchanged original strict checker.
