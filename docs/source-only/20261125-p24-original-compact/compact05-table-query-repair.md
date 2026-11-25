# Compact05: literal-numeral cast alignment

Status: source-only candidate; actual retry and kernel qualification pending.

## Bound input and observed errors

P1 compact05 used `f51e91aad4a63fa5167d8a1377b988db633a817c`.
The exact saved log is `p1-compact-05.log`, SHA-256
`916894d7a1d84a6fde68dd230d3bca2b9c8248b19fe66f6e37c24d21f5e9ab38`.
Both owned files have identical bytes at current HEAD
`24867d3abd0990b1ef80bf3fd1982d74831f7eb4` and at that diagnostic input.

- `P2HistoricSieveTableSemantics.lean` 240/242/244: the generic identity's
  specialization contains a cast natural numeral (`↑6`, `↑12`, or `↑8`),
  while the target uses the corresponding real literal. The reverse rewrite
  therefore still failed; the new repair does not repeat that specialization.
- `ActualThirdOriginalStoredQueryAllBranches.lean` 27: the floor lemma uses
  the rational cast of the integer denominator `12`, while `hloQ` used a
  rational literal `12`. The same issue affects the subsequent ceiling step.

## Minimal repairs

TableSemantics now obtains each existing `reciprocal_error_rounds_up` bound
first, proves a concrete denominator equality with the exact real literal
(`6`, `12`, or `8`) by `norm_cast`, and rewrites that bound in the forward
direction. Its integer denominator and `errL` / `errH` / `interpError`
definitions are unchanged; `exact` then consumes the aligned bound.

StoredQuery changes only the construction of `hloQ` and `hhiQ`: both now
explicitly use `((12 : ℤ) : ℚ)`. Their denominators therefore match the
existing `query_floor_div_literal` / `query_ceil_div_literal` equations before
rewriting. The original exact-cast transfer to real inequalities, scaling,
signed integer division, and all three query branches remain unchanged.

Classification: **formal expression / cast API compatibility**. These repairs
add no mathematical premise or analytic bound. They use the already checked
frozen 1106 sources at publication commit
`3ffa2d159c9974e2ca6d5f930c0f2c16baa0135e`: numerical appendix directed
arithmetic (94–102), and `certify_extended_prefix.py`'s original Q80 curvature
ceilings (51–76). See `compact04-historic-sieve-repair.md` for the exact source
hashes and the Q80/P112 distinction. No table substitution or changed terminal
endpoint is introduced.

The existing `p2-current-symbolic-source-precheck.json` lists both modules
under `direct_failure_groups.no_record`. No CI or archive audit was repeated.

## Static checks and hashes

All **29 theorem headers**, **24 complete definition/structure blocks**, and
imports are byte-identical. `git diff --check` passed for both owned files.

| Source | Before SHA-256 | Candidate SHA-256 |
| --- | --- | --- |
| `P2HistoricSieveTableSemantics.lean` | `664ca9a5c92c41adad80c55a17a04d49d6740b63492d17f01703a1a9c41b66a0` | `5dff5675f39a97862ceda4045a4365d3d289f99cd9253bbce4c36f89fd4c691d` |
| `ActualThirdOriginalStoredQueryAllBranches.lean` | `839167b1e610ba542a19d5f4d6256cbd4ec0bcadb5e1b65b3c71c9517daab904` | `2a1b29dc2d1e3e22b8839f153ae07c52826898196fe6ec7f8de83c470ec6c4b5` |

Only these two Lean files and this note were edited. No Lean/Lake invocation,
remote job, staging, or commit was performed. Compile and kernel credit are false.
