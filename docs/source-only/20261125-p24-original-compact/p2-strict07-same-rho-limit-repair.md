# P2 strict07 same-rho limit equality orientation

Actual input source: `5ac1dba116df4ae476989e9c656afe245299f05e`.
Original task: `2578a4211a3944119815b5ae0849122e`.
Complete log: `p2-strict-symbolic-07.log`, 8109 bytes, SHA-256
`66bdf0660cc71579cb46ba0dba643773dfbc90a8bfa71beeae08a61ccf270acf`.
The completed batch accepted 289/321 symbolic modules, reusing 286 and
accepting three fresh modules; four direct failures and no pending work remain.

In `P4ASameRhoCompact.tendsto_full_density`, `Tendsto.congr'` asks for
baseline plus signed correction equal to full density. The existing `change`
statement displays precisely the reverse equality. Add `symm` immediately
before that statement and retain the original alias expansions and `ring`.
This is the same equality-orientation issue as the signed-correction consumer
that strict07 has now accepted.

The frozen manuscript decomposition remains baseline plus compact correction;
no subtraction order, physical cap, cutoff, limit functional, filter, buffer,
mesh or parameter hypothesis changes. This repair does not evaluate or assume
an additional baseline estimate. It is an expression/API repair, with no
identified mathematical gap.

Mechanical comparison with the actual input confirms exactly one proof-line
insertion. All 13 theorem headers, every definition, import, option and other
proof body remain byte-identical. `git diff --check` passes. Candidate SHA-256:
`005543ffd7d3c4ecc2849b817ae99000bdb7ab662df8cbca87b0d4b84d62013c`.

Independent read-only review confirmed the equality direction and exact alias
expansions, with all seven definitions and four imports unchanged.

The candidate still needs the original strict compiler. Finite candidates and
the complete independent owned-declaration audit remain unaccepted.
