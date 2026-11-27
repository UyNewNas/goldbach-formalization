# Exact-tree source publication

The GitHub Git Data API creates its own commit metadata. Source identity is therefore verified by the complete Git tree, every uploaded blob SHA, and the final compiler source bindings.

| Role | Commit | Tree |
| --- | --- | --- |
| Existing remote base | `b945f39a1e355ff4fcca9865ab59ffc97f2172c0` | `4d896b5edc9866c42b28699243b340d08461c006` |
| Local common source | `89fb011ec7f086621170b5bee819d1cf1230290e` | `41a780dc896aa5ebf77506f51f30fd0c72cac7d6` |
| Local combined source | `b8e4b3c724e8ec5b6fd6e4db403e0139d57bf306` | `39555f9fd51a8dc10ad07797b20d60621a222854` |
| Published combined source, independently verified on P3 | `97d5de82f2fd4e3d72fc86347ab40f00cc939a33` | `39555f9fd51a8dc10ad07797b20d60621a222854` |

The 27 changed blob uploads matched their local Git hashes; the returned tree matched before the lease-protected non-force update from b945f39a. The local source checkout was aligned only after same-tree verification.

The 74,235-byte `common-actual-source-lineage.bundle`, SHA-256 `18e423b9f744d9feca84293b9d33773408de6f11b69246d6b92314098130e0c8`, preserves the four local commits and exact donor/review baselines. It requires the published base b945f39a. `git bundle verify` passed. The local commit identifiers in move ledgers and review reports are local history references; the bundle makes them recoverable. They are not represented as GitHub-published commits.

The evidence-only descendant keeps all 24 final-acceptance source bindings unchanged. The accepted proof source remains 97d5de82; later documentation does not constitute a second Lean run.
