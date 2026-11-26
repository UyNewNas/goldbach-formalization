# Full87Ownership: controlled original-row reduction

Status: source candidate with passing local actual-table diagnostics. The
whole module still requires the P2 normal/replay/owned-declaration gates.
No production file, import, option, statement, premise or definition is changed
by this package. The candidate changes only proof expressions in
`remaining_winner_side` and `source_kind_rows`.

## Exact source identity

Module: `ImbalancedChen.P4AOriginalFull87Ownership`.

- Before SHA256:
  `c3221b44ac12d10e59e6a99684284ef5f58f4760f8ac598ec15feb56f2f9ecd6`.
- After SHA256:
  `a0b20f9f98e92a33396d8078700895bb564feb2911b9689bd6b544b30322841a`.
- `P4AOriginalFull87Ownership.patch` is the exact logical production-file diff.
- Both direct imports remain `P4AOriginalFull87SourceDictionary` and
  `P4AOriginalH5H7SourceDispatch`; no dependency is added.

The two proof bodies contain seven changed blocks. All other bytes, including
the H3 proof and the original option commands, remain unchanged. There is no
new axiom, proof placeholder, native decision, unsafe code or weakened premise.

## Observed root cause and rejected hypothesis

The parent reported the actual round6 Ownership failure with a trailing
`Lean.Meta.Simp.dsimpImpl` stack; the cloud queue had not yet released its
complete first-error log when this candidate was prepared.

A local probe using the complete original literal tables and the exact
`Cell`, `rowCount`, `row`, `evalRow` and `Source` definitions reproduced a
concrete failure of the current proof pattern. Its first failure is the
`nine` family at index 2: after `dsimp [row, nineRows]`, the affine inequality
still contains a large unselected `Matrix.vecCons` expression. Repeated errors
then produce the same dsimp implementation stack family. The 55-second bounded
probe was stopped after those explicit errors; the complete observed stdout
is preserved losslessly in `ownership-diagnostics/ActualRowBaseline.log.xz`.

Raw baseline log: 2,973,696 bytes, SHA256
`88a9a8f86a58cfd13057b7eaa5058abdb4a2fb2ea59d894340a0eed57acaedf2`.
`BASELINE_ERROR_AND_STACK.txt` preserves the first error and a short trace.

An earlier hypothesis blamed the H3 `dsimp ... at *`. That local H3 subproof,
with the complete original H3 source table and `StrictH3` definition, passed.
It is not the demonstrated root cause and is therefore left unchanged.

## Repair mechanism

Each affected proof already chooses original row 15 or 17. The candidate
first uses `change` to expose that selected row as its original nine rational
coefficients. This is a definitional-equality check against the actual source
table, not an assumed replacement row. Each finite source index is still
handled and checked.

After expanding the eight-coordinate sum, `Fin.ofNat` and `Fin.succ` reduce
the numeric indices. `Fin.isValue` and `Fin.reduceFinMk` then put the remaining
coordinate indices into the same canonical form as the target. This matters:
the intermediate probe had the mathematically identical atoms `t ⟨3, proof⟩`
and `t 3` in different syntactic forms, which `linarith` did not combine.
The final scalar proof is `linarith only [hh]`, consuming only the selected
row inequality.

The canonical-index step reuses the same Fin reduction API already present
in the current accepted `P4AOriginalH5H7SourceDispatch` proofs. No larger
recursion option or relaxed warning is introduced.

## Actual-table coverage

| Original family | Row | Number of source-index instances | Resulting scalar fact |
| --- | ---: | ---: | --- |
| `nineRows` | 15 | 13 | `t 0 + t 3 < mu` |
| `h5AffineRows` | 15 | 7 | `t 0 + t 3 < mu` |
| `h7AffineRows` | 15 | 10 | `t 0 + t 3 < mu` |
| `h5AffineRows` | 17 | 7 | `mu < t 1 + t 2` |
| `h7AffineRows` | 17 | 10 | `mu < t 1 + t 2` |
| `fiftyAscRows` | 15 | 1 | `t 1 + t 4 + t 5 < mu` |
| `fiftyDescRows` | 15 | 1 | `mu < t 1 + t 4 + t 5` |

All 49 instances passed together in `ActualRowCanonical.lean`, using the
complete literal source tables, in 37.66 seconds with empty stdout and exit 0.
The local run used Lean `v4.33.0-rc1` and Mathlib
`e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`, matching both local project manifests.
The proof options were `warningAsError=true`, `maxRecDepth=50000` and
`maxHeartbeats=40000000`; local threads were 2. The P2 strict proof flags are
unchanged. No project object was generated or relabelled accepted.

`ownership-diagnostics/MANIFEST.json` records all raw/compressed source and
log hashes, original dependency source hashes, observed exits and timings,
including the two intermediate failing probes and the negative H3 diagnosis.
The compressed final diagnostic contains the complete standalone input for
inspection. This is local normal-checking evidence, not full-module kernel
replay or owned-declaration audit evidence.
