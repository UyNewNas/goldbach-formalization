# P2 strict07: selector local-instance style repair

Actual source: `5ac1dba116df4ae476989e9c656afe245299f05e`; local metadata HEAD: `9221e518435fb8429adc1fe8b182639bfa114f6d`.

The original batch has now completed with 289/321 successful modules (286 reused, 3 fresh). Complete log: `docs/source-only/20261125-p24-original-compact/p2-strict-symbolic-07.log`, 8,109 bytes, SHA-256 `66bdf0660cc71579cb46ba0dba643773dfbc90a8bfa71beeae08a61ccf270acf`. It reports only `linter.style.haveILetI` for the selector at line 227 and explicitly recommends `letI` → `let` because the goal is a proposition. The preceding Decidable mismatch does not recur in this complete run. The proposed single-character repair below was not an input to that run.

The sole source edit deletes the `I` from that `letI`. The anonymous local binding still has exactly type `Decidable (rootTest lo hi D T .base)` and value `Classical.propDecidable _`; the typed `hroot` reflection and final `exact hroot` are unchanged. This follows the actual compiler recommendation and preserves the original filter instance. No definition, gate, theorem header, other proof, import or option changes.

Before source SHA-256: `23c398d3d6da90ff7359444b8d443d6bf045747ed4427cf0ed2ecf059b895945`. Candidate SHA-256: `f16eb47f1407020aa844a2ba8f5fe1b24e1b3c5181a094aa8e61a5e2d18344e1`.

Exact-byte reconstruction from the actual input confirms a single-character deletion. Scoped `git diff --check` passes. No linter exception was added. Only the assigned selector file and this note were edited; no compiler, remote, index or commit operation was performed. The new candidate awaits the original checker.
