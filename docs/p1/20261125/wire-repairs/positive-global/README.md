# Wire positive-cell and global-source proof repairs

These are source-only candidates for the 11 actual errors in
`P1ActualVariableFifthPositiveCellLimit` and the two actual errors in
`P1ActualVariableFifthGlobalSourceAssembly`. Neither repaired source has been
compiled, kernel checked, or audited by this change.

The actual normal task was `job_de5637e9cbe04bde8fbde4e259c08ff4`. Its complete
error sections were exported read-only by `job_033699aad796487db6e8c93e692b8e74`
from the failed normals of source commit
`220c14630ffd266f824bdbf0977147ecb740c0dd`. The export is
`/workspace/scratch/cba105ac8c38/p1-wire-complete-failures.json`, SHA256
`b342fa1e13a709d4433252232f66d023fe0e4df2defdf337327e31db0bfb4e4d`.
`REPAIRS.json` binds every actual error to its original source location and
complete-log section, and records each normal command, source preimage and
candidate Git blob.

## Candidate sources

| Owner | Before SHA256 | Candidate SHA256 |
| --- | --- | --- |
| `P1ActualVariableFifthPositiveCellLimit` | `fed3bd2f8cd4df2f14bb0fdc0fabe415820e1b227da78376d3070d7d194980e4` | `b26a1efe6994065e241fce4e62538921a8d11187db8d6531a5a4e3d0dc106815` |
| `P1ActualVariableFifthGlobalSourceAssembly` | `b6cbe222f09ae90302aecf424672d5c460cf0e77b3a290a5b957af882d3966ed` | `8f2272f57c58bd820e4f6a390dc1aed1a4e2d9f744cb2a1a2897bf3b5f0c3157` |

## Diagnosis and bounded repairs

All reported failures concern formal expression or API use. The diagnostics do
not expose a new mathematical gap. The original exact source, cap, coordinate,
weight and cutoff contracts are retained.

| Original locations | Cause and repair |
| --- | --- |
| Positive: 38 | General simplification left the seed-first nested maximum in the wrong presentation. Reuse the explicit, seeded `Finset.max'_insert` proof already in `P1LiteralVariableFifthCompactSupplier`. |
| Positive: 76, 303 | Function subtraction and composition remained different from their explicit lambdas. Add the existing `Pi.sub_def` normalization; add `Function.comp_def` for the continuity composition. |
| Positive: 139, 145, 146 | The unavailable `indicator_of_not_mem` spelling caused the identifier and follow-on errors. Use `Set.indicator_of_notMem`, including the same branches later in the file. |
| Positive: 210 | `rw` did not reduce the applied integrand lambdas. State the pointwise equality with `change` and type the intersection membership explicitly. |
| Positive: 242, 244 | `IntegrableOn` has no `.congr_fun` field. Reuse `integrableOn_congr_fun ... .mpr` and the original finite-sum integrability witness, with the same pointwise atom argument. |
| Global: 72 | The rewrite decomposed `tupleDifference` on both sides, creating an unwanted second owner sum on the right. Restrict that rewrite to `conv_lhs`, then distribute the existing weight. |
| Global: 178 | Unrestricted simplification changed `Fin.last 4` to a numeral and unfolded unrelated mesh/product internals. Use only the existing case hypotheses and elementary conditional rules for the literal cutoff partition. |

The atom and integrability patterns come from
`P1ActualVariableFourthFifthCellTestLimit`, source SHA256
`021073141f22e8d26e908d1ebc8cdecd730bf271e0db9fa4e78d2a1972d5dccd`.
That exact source is an accepted owner in the historical lane receipt
`docs/p1/20261124/batch8-verified-evidence/verification.tar.xz` →
`batch5-batch6-batch7-next17-normal-supplement-acceptance/lane-1/VALIDATION_RESULTS.json`.
The receipt reports normal/kernel/full-owned validation with standard axioms and
unchanged source plus five outputs. This is evidence for the donor only.

The seeded-max donor and `P1OriginalCoarseFourthCellIntegral` function-subtraction
donor appear at exact matching hashes in that lane's dependency-source map.
Their use here is recorded as source reuse, without inferring separate owner
acceptance from dependency membership.

## Manuscript and verification boundary

The pinned 1106 manuscript commit is
`a988cba584d803ae2856a0de50efb582f4f3dd6a`. The relevant sieve-appendix anchors are
`sv:odd-gain`, `sv:fifth-envelope`, and `sv:finite-realization`: the actual fifth
cap increase, zero extension below 2, maximum over admissible tents with the
inherited cap, positive last-prime cuts, and finite ancestor-compatible
realization. The exact bookkeeping in `argument.tex` is recorded at
`eq:current-lower-exit` and `eq:current-lower-projection`. Raw manuscript file
hashes are in the manifest.

Static comparison against Git220 passed for all 37 declaration headers, all 11
complete definitions/abbreviations, imports and options. Only the six named
Positive proof bodies and two named Global proof bodies in the manifest changed.
No new hypothesis, weakened theorem, source dependency, option increase or proof
bypass was introduced. `git diff --check` passed for these two sources and this
note directory.

An independent read-only review by `p1_inventory` found no material issue at
the two candidate hashes above, after comparing all 13 actual error sections
and the reused donor proofs. It performed no compilation.

The original actual failed normals are the failure evidence. Static checks do
not establish that the candidates compile. Actual normal compilation, kernel
checking and full-owned auditing remain pending. These positive-cut and exact
assembly results do not by themselves close the omitted tails or complete P1.
