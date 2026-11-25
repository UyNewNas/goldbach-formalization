# Strict 07: symmetric pair rescue guard transport

The original strict-symbolic-07 checker compiled source `5ac1dba1` and
finished with 289/321 symbolic modules successful (286 reused, 3 fresh).
Its complete `p2-strict-symbolic-07.log` is 8,109 bytes; SHA-256:
`66bdf0660cc71579cb46ba0dba643773dfbc90a8bfa71beeae08a61ccf270acf`.

`ActualThirdOriginalP4ASymmetricPairRealRescue.lean` failed at old lines
215 and 320: the branch hypothesis matched on `k`, while the supplier's
elaborated argument matched on `k` and its denominator-binding proof.
Both failures concern expression transport, not a missing mean estimate
or a new query-order premise.

## Preserved manuscript correspondence

The frozen 1106 `certify_extended_prefix.py` has SHA-256
`1b77aa5deb90e0f39e06c776847a7e9fff27e23d584036955741b015ca05ad29`.
Its `jensen_difference_upper` retains the selected affine minorant and
positive residual, computes the OLD endpoint queries, and forms the
endpoint chord with the original producer mean. The existing Lean rescue
relates that symmetric-square producer mean to the two computed ordered
means; it uses the paired tent only as a proved real minorant. This repair
does not alter those identities, the selected label, branch/root/residual
tests, OLD query operands or order, or either public query-order contract.
No symmetry of the actual cap is added as a premise.

## Minimal changes

At both call sites, each branch/root/residual argument now splits `k`
and supplies the original hypothesis by `exact`. The complete two guard
calls are byte-identical to the corresponding call in
`ActualThirdOriginalP4ABalancedSymmetricLeaf.lean` at `5ac1dba1`, which
strict07 passed in 7.404 seconds. This also reuses the same pattern already
passed in the symmetric prerequisites module.

The original log applied the source-bound `unusedTactic=false` baseline
exception. The candidate does not inherit it. In the existing
`symmetric_literal_endpoint_swap` proof, the `push_cast` after the broad
definitional `simp` is removed; the original case split, simplification,
and final `ring` remain. This is a local lint-preparation change, with its
strict elaboration and lint outcome still awaiting the next actual run.

## Static checks and bounded follow-up

Exact comparison against `5ac1dba1` confirms only the two guard-block
replacements and the one tactic deletion. All 22 public theorem headers
and both imports are byte-identical; the file has no computational
definitions. No hypotheses, axioms, admitted proofs, checker settings,
or linter exceptions are added. `git diff --check` passes.

A read-only scan restricted to the 32 modules listed as failed or blocked
in the completed strict07 summary found one further identical old guard
call in `ActualThirdOriginalP4ASixTentSymmetricLeaf.lean`, starting at line
191. It was reported to root and not edited here. The supplier use in
`P2OriginalCompactQ80JensenSelection.lean` is a different generic-box proof
and is not classified as an identical call block.

Original source SHA-256:
`e4929aa0ef15a48ed73afe88bc06052f0d50b21967546b9879b604196f0f52fc`.

Frozen candidate SHA-256:
`524e515e7f4d3b016582e67205487552f253d40ef8fbddaaf3a4b7f9841c10e5`.

The candidate has not been compiled and carries no new compilation or
kernel credit. No index, remote task, or P2 running input was changed.
