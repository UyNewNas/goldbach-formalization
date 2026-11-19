# P2.6 exact archive label-index check

Parent `6f483c7bdd5f189b5b24881ff11d4ddfb8c1b9eb`; original source baseline `6848b4a69fd6f25806989dac7d305d27a6cd204e`. The change extends the existing exact-rational summary check with an optional check of the *literal archive label layout*. It adds no Lean theorem and discharges no mathematical premise.

## New bounded check

For exact source text pinned by SHA-256, the script reads the recorded fourteen `originalId` values, the relevant `globalIndex` clauses and the actual `sourceIndexedRecords` list construction. It reconstructs the frozen label ordering, including the already-recorded winner9 seed reorder, and checks:

* fourteen `ascending` IDs occupy 0–6 and 8–14, with the single radial record at 7;
* the 13 original `.ascendingPair i` records land at 45–57 and are respectively `t00` through `t12`;
* the reconstructed 87 archive labels are unique; the existing exact per-cell Q96 summary comparisons still run.

It checks the exact source shape and fails if the pinned source bytes differ. These are source/metadata checks only. The result does not establish chronological policy execution order, membership or sign/mass of any N-dependent prime occurrence, geometric ownership, the original 26 witness payloads, or the 28,918 simplex-row indices/weights. The 87-label source mapping is not a substitute for the Lean theorem or kernel replay.

## Inputs and reproduction

The original four inputs and their hashes are in `CELL_SUMMARY_CHECK_HANDOFF.md`. Additional immutable sources:

* `--fourteen`: formalization `6848b4a69fd6f25806989dac7d305d27a6cd204e`, `docs/source-only/20261102-resume-30r/full87_source_history/P4AOriginalAscendingFourteenAffineSource.lean`; blob `36d9e058f2c0f8ff444413ab298608fd8125a790`; SHA-256 `e5e7c88c94e3debd43ad523ecdcafcf3878852414f473037328761b0d73e5aaa`.
* `--dictionary`: same commit, `docs/source-only/20261102-resume-30r/full87_source_history/P4AOriginalFull87SourceDictionary.lean`; blob `b35c77fc9f3905d87ceb9a3297625cb3267e795d`; SHA-256 `dbfadaa879e08c2c3ecb270f699b84f3f9ac7b0b044ba96be8046da4a73c501c`.
* `--sourceindex`: formalization topic commit `be2efd01c561080672e6c0ad0ba21638837afe4c`, `docs/source-only/20261108-full87-archive-source-index/P4AOriginalFull87ArchiveSourceIndex.lean`; blob `c7fa8c986b790d2ba09f6491c092b1c81563aeca`; SHA-256 `a003919a12b213dd2a979fe07e7376ec3e619d24f704faacf5c5430b3ed009f1`.

Fresh command and output, exit 0:

```text
python3 /tmp/p2_saving19/check_cell_summaries.py --manifest /tmp/full87.json --stage /tmp/p2_saving19/stage.lean --consumer /tmp/p2_saving19/consumer.lean --review /tmp/p2_saving19/review.json --fourteen /tmp/p2_saving19/fourteen.lean --dictionary /tmp/p2_saving19/dictionary.lean --sourceindex /tmp/p2_saving19/sourceindex.lean
PASS: 13 ordered cell counts, 39 exact rationals, 13 replacement deltas
PASS: 26 recorded witness hash bindings, 28918 recorded rows, 289180 factors
Q96 old/new/increment: 279507753196319072435668 283388722705335806564439 3880969509016734128771
SCOPE: summary metadata only; no witness bytes, row replay, Lean or kernel validation
PASS: original fourteen indices, single radial index 7, thirteen indices 45–57
SCOPE: 87 archive labels only; no policy order, prime occurrences or simplex rows
```

The earlier four-argument invocation still exits 0. `python3 -m py_compile` exits 0. Updated script SHA-256 `059a34d447dcc056db51654bd62f6fea013d0fd6b23a7244c67776628bed1bfb`, Git blob `eec42da3b5d087e371e2b80a969237704e16bcb1`; the earlier handoff's script hash describes its earlier commit, not the updated file.

## Verification boundary

SOURCE_ONLY audit; new Lean proof=none; COMPILED=no; KERNEL_REPLAYED=no; TRANSITIVE_AXIOM_CHECK=NOT RUN; independent review=NOT RUN; finite Lean bodies=UNEVALUATED. No Lean/Lake installation or pin change occurred; the 26 witness contents and matching local toolchain remain unavailable. No previous v3-only run is credited to saving19. The next material action remains byte-verifying the original 26 inputs and their 28,918 rows, then installing and checking the exact downstream closure with logs and axioms. If a downstream consumer separately requires an after-fourteen finite-policy equality, verify its exact premises and occurrence semantics rather than assuming it from this archive index check.
