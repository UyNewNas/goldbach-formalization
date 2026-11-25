# P2 strict03 frontier and policy proof repairs

Evidence: original P2 checker job `c2edcc3a270e4e2aabb7155f3b8bc0e0`,
source `fcd0acba7dfc34cf14075b880e7a31aef1550b87`.
The complete 19151-byte log is `p2-strict-symbolic-03.log`, SHA-256
`3553e024808d4e959ba69b79575bc26a170604a7035e49a9e076d51b7d4f8205`.

## Actual failures and narrow changes

- `ActualExtendedThirdCompactFrontier`: the existing weighted reindexing
  theorem's explicit final function argument was omitted. Supply the exact
  existing cell-restricted signed test, `fun p => if actualPrimeTupleLog N p ∈
  actualExtendedThirdOwnedCell m j then G p else 0`. The finite carrier,
  tuple dimension, prefix weight, cell boundary, and arbitrary signed test
  are unchanged.
- `ActualExtendedThirdCompactResidualProfile`: use sequential `ring`
  after `field_simp`, as required by the actual unnecessarySeqFocus error.
- `FrozenRosserPolicy`: remove the reported unused nil equation from the
  cons branch's `simp only` arguments.

The first change applies the already proved
`firstExitFrontierCandidates_weighted_sum_eq_tuple_sum` with its
actual argument; it adds no new mathematical premise. It respects the
frozen 20261106 manuscript's first-exit identity and retained-prefix policy
in `sieve-appendix.tex` at manuscript commit
`3ffa2d159c9974e2ca6d5f930c0f2c16baa0135e`.
These failures are formal expression/tactic issues, not evidence of a
substantive manuscript gap. All public theorem statements, definitions,
imports, strict inequalities and checker/linter settings are unchanged.

This note records candidate repairs and static comparison only. It gives
no new compilation, finite-certificate, or independent-audit acceptance.
The unchanged original checker must verify the published candidates.

## Static source bindings

- `ActualExtendedThirdCompactFrontier.lean`: 8 unchanged theorem headers; SHA-256 `52283f363db3ec852a038f9a0ede35c91e4da104c252c8ecff8cf8d163ac8154`.
- `ActualExtendedThirdCompactResidualProfile.lean`: 10 unchanged theorem headers; SHA-256 `17e48fe4686e42be846c99217505dce7cfbfbca929a8172560eb92d42a59ce09`.
- `FrozenRosserPolicy.lean`: 17 unchanged theorem headers; SHA-256 `0a2ff50f609d9728507aed78257bd844dc2b5ad11f24ac40cd38096ea8fa25ff`.
