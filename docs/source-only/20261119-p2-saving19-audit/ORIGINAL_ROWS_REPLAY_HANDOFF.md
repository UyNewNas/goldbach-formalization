# P2.6 saving19: recovered original rows and exact arithmetic replay

Parent: `cfc572ea691b2ac3432a8df690d23f48370fc300`; original source baseline `6848b4a69fd6f25806989dac7d305d27a6cd204e`. This commit's own SHA and its handoff blob are identified by Git, avoiding a self-hash cycle. It adds no Lean theorem and discharges no Lean premise. Earlier handoffs in this directory still apply, except their statement that the 26 input bytes had not been found is now superseded. The checkout is incomplete; the source remains the source-only candidates and exact pins cited in `HANDOFF.md` and `T03_DOWNSTREAM_HANDOFF.md`.

## Recovery and provenance

The previously registered original release package is now recovered from the existing numerical supplement `chen-imbalanced-semiprimes-numerical-v3-20261029-115616.zip` ([available supplement](https://chatgpt.com/library?file_id=libfile_a22616deebf08191bf2369e8234f85f8&account_id=personal)), member `full-witnesses.zip`: 323605374 bytes, SHA-256 `8f1bdf63e1aa972256b2422f824f3d177617b31bf41b6a2b8cf29b0562647ad1`, exactly the digest in `FULL87_PUBLICATION_PROVENANCE.json` for release asset 626620833. A different November 1 supplement was inspected and did not contain matching names/hashes; it is not a source for this replay.

The 13 geometry and 13 moment files were extracted from their `release_member` paths from the original nested ZIP into the expected sibling `goldbach-research/` directory. All 26 individual byte lengths and SHA-256 hashes match `original_eighth_compile_input_release.individual_inputs` in the manifest. Their total is 80189086 bytes. The original large payloads are not uploaded in this source-only packet. The replay also cross-checks each file's hash against the pinned review's `bindings_sha256`.

Immutable small inputs:

* `FULL87_PUBLICATION_PROVENANCE.json`: Git blob `44c46f115ba79dd62ed581c889c34612c21d2434`, SHA-256 `fccf400489947123dd088d7f6087b76dc7b777259a0348d9c31601f75565684f`.
* Manuscript repository pin `9731290e8f53cffda44129906cde6a965eaa869b`, `verification/data/eighth-third-moment-refinement-independent-20261009.json`: blob `d654ce7bb88e5f462b3bbd085c7a01f2364cadfc`, SHA-256 `e3241b43644f708a37bd83ad8177ea6e3f8adcd6f44fa5f0c931964027a3e84e`.
* Original nested package's `chen-numerical-evidence-20261010-renewal-v2/goldbach-research/eighth-unequal-moment-independent-engine-20261009.py`, SHA-256 `5e778995582ddf49d87e023edf4558fe6cceeecaf5a823e94c7970367d53e520`. Its own `beta_checks` ran both standalone and through the harness. The original review engine is reused, so this is not an independent human review.
* Supplied manuscript `9731290e8f53cffda44129906cde6a965eaa869b:paper/source/manuscript-body.tex`, blob `d529bea2ecfcc74d64fc1664ac770a3becaa7c79`, SHA-256 `ee6aecc164cc59f2d1fed1ad9e48f18f98472ab1d77ab425d53d93bc41ce56bd`, matches the chain's S12/Q09 pin. No parameters were changed.

## Per-row result and limits

`check_original_rows.py` (SHA-256 `734830754f320394f8d3563da41444e44e766b7cad1e7550444751e0b2eb035e`, Git blob `fb753ef5e1cad8d31552c6dec1e23788f3423a80`) reconstructs vertex gaps and all ten factors from eight coordinates; checks same cell and row IDs, nine distinct ordered in-range geometry vertex IDs, maxima and gap-weighted means; recomputes every physical 8-simplex volume using an exact 8x8 Bareiss determinant divided by 8!; and uses the pinned engine to compute every old and new Q96 floor and all ten Q80 log-factor floors. Each result is compared with the matching original record, then each per-cell stream and total and the global stream and totals are compared with the pinned review. This checks 28918 rows, 28918 physical determinants and 289180 factor floors. The determinant routine was also compared with exact rational Gaussian elimination on 100 deterministic 8x8 matrices, including singular matrices; this is a separate test, not a proof.

The Q96 old/new/increment integers are respectively `279507753196319072435668`, `283388722705335806564439`, `3880969509016734128771` (each divided by 2^96). The new quantity is the replacement same-row floor sum, not an additional old-floor payment. The 13-row counts and full log are in `ORIGINAL_ROWS_REPLAY.log` (SHA-256 `0c5d3abf6802ca9dce61738b7bbbd0494b0f3a246f3e957d8f12495a491c454e`, Git blob `38ed16eaf6b0ff08606280d5144e5fe8f760e70b`).

These are exact Python integer/rational checks on the recovered bytes. They do not validate coverage or null-overlap, admissibility or chronology of prime tuples, or the claimed real integrals in Lean. In particular, gap-weighted simplex factor means are not either of the distinct prime-history dictionaries: the reciprocal-prime bank weights and the unit-weight physical list must not be interchanged. The existing T03 source candidate `original19_archived_cell_le_integral` and its downstream consumers are described precisely in `T03_DOWNSTREAM_HANDOFF.md`; they are not compiled here. Do not conflate the S12 held-sixth local policy with the T03 full87 policy without establishing the exact same-parameter relationship. Do not carry run 44455834837's hash-bound v3 sixth-eleven acceptance to saving19.

## Commands and status

Run in the existing environment with Python 3.12.14, single process and no resource enlargement (shell virtual-memory limit unlimited; cgroup v2 `memory.max` and `cpu.max` files were not present at the checked paths):

```sh
python3 -u /tmp/p2_saving19/check_original_rows.py \
  --manifest /tmp/full87.json \
  --review /tmp/p2_saving19/review.json \
  --engine /tmp/p2_saving19/eighth-unequal-moment-independent-engine-20261009.py \
  --witness-dir goldbach-research
```

Exit 0; output recorded in the log. The wrapper used `bash -o pipefail` and `tee`. `python3 -m py_compile` on the harness exited 0. An attempted `/usr/bin/time -v` wrapper exited 127 because `/usr/bin/time` is absent; it produced no replay evidence and the successful direct command above was run afterward. `lean --version` and `lake --version` both returned 127 (command not found), and `elan` was absent from PATH. No toolchain was installed, no pin changed, no CI/Actions launched. Declared pins are Lean `leanprover/lean4:v4.33.0-rc1`, mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`, and native `subfish-zhou/goldbach-lean@09b97db5764ade1246bfb77206baa1b124760958`; they are not evidence of installed versions. c and K, if used, remain 49044063/25000000 and 8452171/1250000.

SOURCE_ONLY=yes; COMPILED=no (UNCOMPILED); KERNEL_REPLAYED=no; TRANSITIVE_AXIOM_CHECK=NOT RUN; INDEPENDENT_REVIEW=NOT RUN; Lean finite proof bodies=UNEVALUATED. No new external mathematical input or external proof project was introduced; the inherited input statements, application, normalization and verification status remain those of the cited earlier registries and still require transitive tracing for acceptance.

Next: retain the authenticated witnesses and recover the exact effective import closure in an already authorized matching environment. Compile the precise T03 bridge and actual consumer closure, record all commands/limits/logs, kernel replay and print transitive axioms. Trace actual same-parameter history, frozen ancestor, actual sixth-parent and prime occurrence/reindex semantics with the two weight dictionaries; determine whether the existing full87 consumer already supplies each required connection before proposing any new proof. Missing compilation by itself is not a new yellow mathematical obligation, and no saving16 per-corner PP work is assigned here.
