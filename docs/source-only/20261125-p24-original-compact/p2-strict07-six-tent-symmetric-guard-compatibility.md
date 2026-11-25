# Strict 07: exact symmetric guard-call compatibility

Status: **STATIC_COMPATIBILITY_REPAIR / MODULE_COMPILE_PENDING**.

`ActualThirdOriginalP4ASixTentSymmetricLeaf` was blocked in strict07; it had
no new compilation diagnostic or successful compile in that run. This is
the explicitly authorized repair of one exact matching call site, not a
claim that this module reproduced the earlier error.

The sole `original_selected_tent_guard_bridge` call in
`original_six_tent_symmetric_stored_integer_upper` uses the same source
vectors `![x0,x0,z0]` and `![x1,x1,z1]`, fixed D/T, physical symmetric
coordinates, coordinate-binding suppliers and three literal guard hypotheses
as the calls in `SymmetricTentPrerequisites` and `SymmetricSafeChordDirection`.
Those modules passed in strict06 (5.111 seconds) and strict07 (7.414 seconds),
respectively. The full logs are `p2-strict-symbolic-06.log` (SHA-256
`501f0a48515e5cae43d70408517a6d46cabc6c5c419b85d3cbe736e40cfc12f7`)
and `p2-strict-symbolic-07.log` (SHA-256
`66bdf0660cc71579cb46ba0dba643773dfbc90a8bfa71beeae08a61ccf270acf`).

Only the three old `simpa` argument proofs are replaced by `cases k`
followed by `exact hbranch`, `exact hroot` and `exact hres`. This uses the
already tested reduction of the dependent branch match and literal vector
coordinates. Ascending-test priority, root/residual inequalities and all
premises are unchanged.

An exact comparison against `5ac1dba1` confirms that these are the only
replacements: all other source bytes, including headers, computational
definitions, imports and options, are unchanged. The complete repaired
supplier call is byte-identical to both passed reference calls.
`git diff --check` passes.

- Before SHA-256: `b0b8aa5a1b8bfe6f91480121c37d0476e2ac48d317d24d0295fbf3fbd3305b63`.
- Candidate SHA-256: `41ff63245dbb20991694e97339fc9540c125d1f7dfb688cbf175575f2bc1af21`.

No other module was scanned for repairs or modified, and no compilation,
remote task, index operation, commit or gate change was performed. This
module's strict compilation and all acceptance credit remain pending.
