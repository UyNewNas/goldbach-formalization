# P2.6 saving19: exact cross-check of 13 recorded cell summaries

Parent `2aa4b5f55fbc0a632724027f50be877346d20a8e`; original source baseline `6848b4a69fd6f25806989dac7d305d27a6cd204e`. This packet adds one repeatable Python metadata/rational check and this handoff. It adds no Lean theorem and eliminates no proof premise.

## What was checked

The accompanying `check_cell_summaries.py` reads four exact, SHA-256 pinned inputs and compares the thirteen ordered `thirdRows` in the original frozen Lean numerical source to the thirteen cells in the manuscript repository's independent-review summary. For each cell it checks the index, declared simplex count, and the before/final/increment rationals with exact integer fractions, plus before + increment = final. It also compares the 26 *recorded* geometry/moment witness SHA-256 bindings between the review summary and the publication manifest. The two records' common provenance is not treated as independent verification of the witness bytes.

Fresh execution:

```text
python3 check_cell_summaries.py --manifest /tmp/full87.json --stage /tmp/p2_saving19/stage.lean --consumer /tmp/p2_saving19/consumer.lean --review /tmp/p2_saving19/review.json
exit 0
PASS: 13 ordered cell counts, 39 exact rationals, 13 replacement deltas
PASS: 26 recorded witness hash bindings, 28918 recorded rows, 289180 factors
Q96 old/new/increment: 279507753196319072435668 283388722705335806564439 3880969509016734128771
SCOPE: summary metadata only; no witness bytes, row replay, Lean or kernel validation
```

The old/new/increment numbers are numerators over the common denominator 2^96. The increment equals new minus old; the new value is a replacement, not an additional sum on the same rows. The total 28,918 and 289,180 are sums/fields in these records, not individually evaluated objects. No assertions are made about the truth of the review summary's historical PASS, the source inequalities, simplex geometry, Q80/Q96 row checks, or the two prime-weight dictionaries.

## Exact input provenance

* `--manifest`: formalization commit `6848b4a69fd6f25806989dac7d305d27a6cd204e`, `docs/source-only/20261110-yellow-closure-10t/FULL87_PUBLICATION_PROVENANCE.json`; Git blob `44c46f115ba79dd62ed581c889c34612c21d2434`; SHA-256 `fccf400489947123dd088d7f6087b76dc7b777259a0348d9c31601f75565684f`.
* `--stage`: formalization topic commit `be2efd01c561080672e6c0ad0ba21638837afe4c`, `docs/source-only/20261108-full87-stage-reconcile/P4AOriginalFull87ArchivedStageNumericReconcile.lean`; Git blob `ab1f0914f058106ff559e4ab3d4de112027692d5`; SHA-256 `1629234868c4bf7becaf9836b7fff328b63f9d3559c11d9d1b40ee6b5f5ccbf0`.
* `--consumer`: formalization commit `6848b4a69fd6f25806989dac7d305d27a6cd204e`, `docs/source-only/20261102-resume-30k/saving19_moments/P2OriginalSaving19MomentFloorConsumer.lean`; Git blob `ba62c7530fe1c4162f976f64a1736b07f941ea80`; SHA-256 `71cb35db43b7ccfe0340a60223e080407607869c11bf75b06542bf4c5c0a1d2d`.
* `--review`: manuscript commit `9731290e8f53cffda44129906cde6a965eaa869b`, `verification/data/eighth-third-moment-refinement-independent-20261009.json`; Git blob `d654ce7bb88e5f462b3bbd085c7a01f2364cadfc`; SHA-256 `e3241b43644f708a37bd83ad8177ea6e3f8adcd6f44fa5f0c931964027a3e84e`.
* The audit script SHA-256 is `c2871b3ebaa745a15a3e26323cf98db0844f788b8426cef2a72d722602f917df`; Python syntax check `python3 -m py_compile check_cell_summaries.py` exited 0. The script rejects any of the four source files if its hash differs.

GitHub release asset 626620833 metadata independently reports the same package digest recorded in the manifest. The package and 26 witness files were not downloaded; matching two recorded digests is not a hash check on the witness contents.

## Status and remaining work

SOURCE_ONLY audit; new Lean proof=none; COMPILED=no; KERNEL_REPLAYED=no; TRANSITIVE_AXIOM_CHECK=NOT RUN; independent review of this new check=NOT RUN; original finite proof bodies=UNEVALUATED. Python arithmetic here is not Lean compilation, kernel replay, numerical integration, or a per-simplex verification. The historical v3 run is not being applied to the saving19 downstream.

`lean --version` and `lake --version` returned exit 127. The authorized environment still lacks the original witness texts and effective import closure. Obtain those existing pinned inputs in the authorized environment, check each row's geometry, actual index, ten factors and Q80/Q96 association, and then elaborate and replay the exact downstream consumer with the required hashes and transitive axioms. The possible separately staged finite-policy interface remains a question of what the intended downstream consumer actually requires; no new mathematical gap is claimed merely from missing compilation. No reserve or wider P2 result is concluded.
