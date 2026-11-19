# saving19: original archive decoder field preflight

Parent `2e44964c47ab17994dc623fd5909dba6b9f3ec4e`; original source baseline `6848b4a69fd6f25806989dac7d305d27a6cd204e`. Git identifies this commit and handoff blob. This is an additional read-only data check; no Lean theorem, field, assumption or formal premise was added or discharged.

## Exact source and scope

Read the complete `P2OriginalSaving19SourceJson.lean`, blob `b85dc68b9e15f37e7172c9ba89ca4eb0ff13adbf`, SHA-256 `ae38e3ed3f11d8bc3350b9d35d1fed164a4494210ed993b2b99e8cd709f93424`, and `P2OriginalSaving19Archive.lean`, blob `45220db20a3d99a759f875d2c7d5f1bd72a6cdf7`, SHA-256 `b8821bbc996d6fdbc19fd359b1be9dd4be181064f7fe1b2f36b8b5a27996a9b6`, under `docs/source-only/20261102-resume-30m/saving19_original28918/`. The source's total parser rejects noninteger JSON numbers, unsupported escapes and duplicate object keys. Its `geometryParse`/`momentParse` decode not only the row values but the original vertices, vertex values, facet indices, facet vertex lists and face ledger; the `geometry_parse_success` and `moments_parse_success` proofs are closed `by decide` terms and remain UNEVALUATED. The fallback via `.toOption.getD default` is only eliminated in Lean if those exact guards succeed.

The manuscript pin remains `9731290e8f53cffda44129906cde6a965eaa869b:paper/source/manuscript-body.tex`, Git blob `d529bea2ecfcc74d64fc1664ac770a3becaa7c79`, SHA-256 `ee6aecc164cc59f2d1fed1ad9e48f18f98472ab1d77ab425d53d93bc41ce56bd`, matching the chain registry. Paragraphs 365–374, 435–449 and 1354–1360 were reread; no quantities, history, signs or original boundaries were changed.

## Actual data check

`check_archive_decode_fields.py` has SHA-256 `2e2ccde6834d963281bb7b45459621fc119be57aaf4ca41d791e7c141da68a58` and Git blob `da66035b2ae2edfce814b89fb755bf8f7912cdf7`. It checks the SHA-256 of both exact Lean files and the publication manifest `fccf400489947123dd088d7f6087b76dc7b777259a0348d9c31601f75565684f`; for each of the 13 geometry and 13 moment originals it checks byte count and SHA-256 against that manifest. Full witness source and previous row/factor replays are recorded in `ORIGINAL_ROWS_REPLAY_HANDOFF.md`.

The Python JSON preflight uses a conservative supported fragment: every file is ASCII and contains no literal Unicode escape; floating-point/non-finite JSON tokens and duplicate object keys are rejected. It checks the type and presence of every field read by `decodeGeometry`, `decodeGeometryRow`, `decodeFace`, `decodeVertexValues`, `decodeMoments`, and `decodeMomentRecord`, including nested arrays, naturals, signed decimal integer strings and rational strings with nonzero denominators. Python's integers and `Fraction` are exact. Result: all 26 files pass, containing 28,918 moment records. Per-cell output is `ARCHIVE_DECODE_PREFLIGHT.log`, SHA-256 `813537ce4e4cd7c34a0f5ad1fc6061dea3b8297b3db6ae97f9db56a831647c93`, blob `5851a4af368a42c5b80502fa370d0bb9af68fca3`.

This is not an execution or a formal equivalence proof of Lean's parser, fuel management, recursion, decoded values or `by decide`; successful Python parsing does not prove that Lean's parser or proof guard elaborates within available resources. Row-by-row Q80/Q96, physical determinant, gate, pulling and higher-moment checks were separately recorded in the previous handoffs; none is promoted to Lean evidence here. The same-source histories and the two weight dictionaries retain the prior `ACTUAL_OCCURRENCE_TRACE_HANDOFF.md` and `FOURTEEN_THIRTEEN_SIGN_HANDOFF.md` boundaries.

## Reproduction and status

Python 3.12.14, standard library, one process, existing environment, `ulimit -v` unlimited; no resources were enlarged:

```sh
python3 -u /tmp/p2_saving19/check_archive_decode_fields.py \
  --manifest /tmp/full87.json \
  --parser-source goldbach/docs/source-only/20261102-resume-30m/saving19_original28918/P2OriginalSaving19SourceJson.lean \
  --archive-source goldbach/docs/source-only/20261102-resume-30m/saving19_original28918/P2OriginalSaving19Archive.lean \
  --witness-dir goldbach-research
```

Full command with `bash -o pipefail` and `tee` exited 0; `python3 -m py_compile` exited 0. Fresh `lean --version`, `lake --version`, and `lake env lean docs/source-only/20261102-resume-30m/saving19_original28918/P2OriginalSaving19Archive.lean` each exited 127, command not found. No toolchain installed, pins changed, resource limits enlarged or CI started. Declared pins remain Lean `leanprover/lean4:v4.33.0-rc1`, mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`, native `subfish-zhou/goldbach-lean@09b97db5764ade1246bfb77206baa1b124760958`; installed revisions are not evidenced.

SOURCE_ONLY=yes; COMPILED=no (UNCOMPILED); KERNEL_REPLAYED=no; TRANSITIVE_AXIOM_CHECK=NOT RUN; INDEPENDENT_REVIEW=NOT RUN; finite Lean proof bodies=UNEVALUATED. No new external theorem or proof project was introduced; inherited external assumptions, exact statements and current verification boundary remain in earlier registries and `ACTUAL_OCCURRENCE_TRACE_HANDOFF.md`.

Next: in the already-authorized matching environment, stage the recorded effective source/import map and the exact 26 files, then minimally compile the real parser, row guard, integration bridge and matching downstream consumer. Record resource limits, complete logs, kernel replay, transitive axioms and independent review separately. Trace any genuinely demanded same-parameter fourteen→thirteen/T03 consumer equality before writing a proof; missing compilation is not a mathematical obligation.
