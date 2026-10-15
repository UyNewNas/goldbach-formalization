# P2 handoff: global scalar-table reduction

State: WAITING_FOR_P0. Request: REQUESTED. Verification: SOURCE_ONLY.

- Request: automation/parts/p2/requests/20261015T042900Z-global-length-scalar.json
- Immutable run: automation/parts/p2/runs/20261015T042900Z-global-length-scalar.json
- Worktree: /workspace/shared/chen-coordination/p2-data-split
- Changed:one Lean proof line,one generator template,two generated reports.
- Effective51-file snapshot SHA-256: 009abaaf000915e163621987136bd6fa6920956d465b562bd030b927d3cf327c
- Patch: automation/parts/p2/runs/20261015T042900Z-global-length-scalar.patch
- Patch SHA-256: a0234c78b4587f38df0d0e1e2cad695e71e89dfcd621577be2c6e7d3a367afc6
- Static map: automation/parts/p2/runs/20261015T042900Z-global-length-scalar-static.json
- Static map SHA-256: 01d6e3c9895fc1644e837c820f0ddabceac02928734ce9d3c69e8b8aa410ee97
- Dependency fingerprint: 54691f2f87426d5e4ce7a8fcc1a3b782dfbc30dccaebbaffbf33b89c854d43a7

Run38680984398 fully accepted the ten remaining length blocks00-09 and FullData.
Partition strict compile3.522s/replay4.473s succeeded; its audit was not reached.
Lengths strict compile1.618s failed only on12 literal Nat lists appended to[]
equal to expectedLengths. RowAssembly and NaturalSums were not reached. Exact
archive, receipt, diagnostics and scoped successful stages are hash-bound.

Only blocks_lengths second calc branch now uses (rw [...]; rfl), the sequential
form already accepted in the12 length blocks. Its first structural branch and
entire approximation_lengths proof remain unchanged. All42 other generated Lean
sources, data, selectors, numbers, theorem types and options are byte-identical.
No linter/warningAsError/resource/trust setting changed. Producer --check,
Python AST, exact single-line map, all186 scalar entries, whitespace and reverse
patch checks passed. No Lean/Lake/checker/audit/CI/push was run by P2.

P0 alone completes Partition audit and full Lengths→RowAssembly→NaturalSums gates.
Previously accepted leaves remain immutable prerequisites, not repeated targets.
New proof compilation and remaining kernel/import memory are unverified. Finite
numerator scope and all analytic/full-budget/hLower/hUpper gaps are unchanged.
Candidate frozen pending actual P0 verification.
