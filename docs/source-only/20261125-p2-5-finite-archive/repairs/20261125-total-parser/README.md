# Original SourceJson: explicit total recursor candidate

Status: **SOURCE_REPAIR_PREPARED_NOT_COMPILED**.

The actual P3 owned audit rejected five compiler-generated `_unsafe_rec`
declarations, each marked `partial = true`. The source parser itself used
ordinary total structural equations. Its old 138-declaration inventory and
failed receipt remain intact; no helper is excluded from the safety audit.

This candidate keeps all 19 public declaration headers and the original
parser behavior. `quoted` uses `Nat.rec`, `digitsNat` uses `List.rec`, and
one private `Nat.rec` bundle provides the original `value`, `array`, and
`object` functions through the three fixed product projections. Every
recursive edge still consumes exactly one original fuel step. The branch
order, eight escapes, integer token handling, duplicate-key check, and
error strings are preserved.

`SEMANTIC_CORRESPONDENCE.json` records the original failure, the existing
explicit-recursor precedent, every changed definition, the per-branch
source correspondence, and the actual static checks. `SOURCE_PATCH.diff`
is the exact source difference. The `after/` snapshot is byte-identical to
the production candidate. The prior `reused/` source is unchanged.

No Lean process, parser execution, numerical replay, Git commit, or remote
job was run for this candidate. Root will perform independent review and
the unchanged strict compile, stock replay, and complete owned type/axiom
audit after publication. Static checks do not certify the new generated
inventory or confer Q96 acceptance.
