# Strict 07: unused clipped-gap binder

Status: **SOURCE_REPAIR_PREPARED / FRESH_LEAN_CHECK_PENDING**.

The completed strict07 run for source `5ac1dba1` reports 289/321 successful
modules (286 reused, three fresh). For this module it reports only the unused
public `hi` binder at input line 181. The previous `clear hi` did not satisfy
this linter. The two strict06 elaboration errors are absent.
Complete log: `p2-strict-symbolic-07.log`, 8,109 bytes, SHA-256
`66bdf0660cc71579cb46ba0dba643773dfbc90a8bfa71beeae08a61ccf270acf`.
The completed batch did not close the entire selected scope; it precedes
the binder repair below.

As explicitly authorized, rename the second explicit parameter of
`argument_gap_le_original_delta` from `hi` to `_hi` and remove `clear hi`.
Its type remains `Fin 3 → ℤ`; its position, explicitness, parameter count
and mathematical proposition are unchanged. The parameter does not occur
in the premises or conclusion. No artificial proof reference or case was
introduced.

Repository-wide `rg` over Lean files found three production calls and five
calls in frozen source drafts. All supply this parameter positionally; none
uses `(hi := ...)`. No caller or frozen file was changed.

An exact byte comparison with `5ac1dba1` permits only the binder spelling
replacement and deletion of the `clear` line. Thus **one public theorem
header is not byte-identical**. All other headers, complete computational
definitions, imports, options and proof steps are unchanged.
`git diff --check` passes.

- Before SHA-256: `9fa3ea4095fcebda6c803047b279cdafe6fb3e27e7e23385adcb862398135b03`.
- Candidate SHA-256: `998d5f981fd3fb4b26a5ece8d3b229833f14b7038f9cfb62bf40e600cdab0d19`.

No compilation, remote task, index operation, commit or gate change was
performed. Strict-lint acceptance remains pending the original checker.
