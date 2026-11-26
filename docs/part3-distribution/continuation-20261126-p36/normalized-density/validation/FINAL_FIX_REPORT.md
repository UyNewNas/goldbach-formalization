# Final review fix wave

Fix base: `0cfdb6ba4b5eb426e220b9211610de633681d68a`.
Implementer: `/root/p36_evidence_audit`.

The only final-review finding concerned the lifetime of restored private source snapshots. `README.md` now fetches the source bundle into `refs/p36-evidence/normalized-density-20261126` and explains that this local evidence ref keeps the snapshots reachable across subsequent fetches while retaining the current checkout.

Changed implementation scope: the README restore command and accompanying prose only. Root separately retained the original final-review report and this execution record. No proof source, exporter, original verification driver, evidence payload, Git ref or checkout was changed by the fix.

Validation reported by the implementer:

- `git diff --check`: exit 0, no diagnostics.
- `git check-ref-format refs/p36-evidence/normalized-density-20261126`: exit 0, no diagnostics.
- No fetch, Lean invocation or test rerun; this is a documentation-only correction.

The scoped re-review follows this bounded fix commit.
