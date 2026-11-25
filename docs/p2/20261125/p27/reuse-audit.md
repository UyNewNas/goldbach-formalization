# P2.7 existing proof and evidence reuse audit

Source checkout: `a929011ec95843553fc2e10b7291c8077e0952c0`. Audit time: `2026-11-25T07:23:08.578330+00:00`.

## Result

The finite natural-sum proof is already implemented and historically accepted. The immediate unfinished verification chain is the split original strip checks, `PairedV2FullCertificate`, and the existing adopted-grid/union/Fubini/semantic-gain consumers. This audit wrote only this Markdown report and its JSON companion; it ran no Lean or cloud task and changed no proof source.

## Exact current-source matches to historical leaf acceptance

Every row below was checked by SHA-256 against its stored terminal acceptance index. These are historical defining-module receipts, not newly verified current transitive object closures. The JSON companion preserves full source hashes, receipt hashes, declaration counts, and recorded object hashes.

| Module | Run | Declarations | Source hash match |
| --- | ---: | ---: | --- |
| `PairedV2NaturalSums` | [38683648702](https://github.com/UyNewNas/goldbach-formalization/actions/runs/38683648702) | 2 | yes |
| `PairedV2NaturalSumPartition` | [38683648702](https://github.com/UyNewNas/goldbach-formalization/actions/runs/38683648702) | 2 | yes |
| `PairedV2NaturalSumLengths` | [38683648702](https://github.com/UyNewNas/goldbach-formalization/actions/runs/38683648702) | 3 | yes |
| `PairedV2NaturalSumRowAssembly` | [38683648702](https://github.com/UyNewNas/goldbach-formalization/actions/runs/38683648702) | 2 | yes |
| `PairedV2NaturalSumLengthsBlock00` | [38680984398](https://github.com/UyNewNas/goldbach-formalization/actions/runs/38680984398) | 1 | yes |
| `PairedV2NaturalSumLengthsBlock01` | [38680984398](https://github.com/UyNewNas/goldbach-formalization/actions/runs/38680984398) | 1 | yes |
| `PairedV2NaturalSumLengthsBlock02` | [38680984398](https://github.com/UyNewNas/goldbach-formalization/actions/runs/38680984398) | 1 | yes |
| `PairedV2NaturalSumLengthsBlock03` | [38680984398](https://github.com/UyNewNas/goldbach-formalization/actions/runs/38680984398) | 1 | yes |
| `PairedV2NaturalSumLengthsBlock04` | [38680984398](https://github.com/UyNewNas/goldbach-formalization/actions/runs/38680984398) | 1 | yes |
| `PairedV2NaturalSumLengthsBlock05` | [38680984398](https://github.com/UyNewNas/goldbach-formalization/actions/runs/38680984398) | 1 | yes |
| `PairedV2NaturalSumLengthsBlock06` | [38680984398](https://github.com/UyNewNas/goldbach-formalization/actions/runs/38680984398) | 1 | yes |
| `PairedV2NaturalSumLengthsBlock07` | [38680984398](https://github.com/UyNewNas/goldbach-formalization/actions/runs/38680984398) | 1 | yes |
| `PairedV2NaturalSumLengthsBlock08` | [38680984398](https://github.com/UyNewNas/goldbach-formalization/actions/runs/38680984398) | 1 | yes |
| `PairedV2NaturalSumLengthsBlock09` | [38680984398](https://github.com/UyNewNas/goldbach-formalization/actions/runs/38680984398) | 1 | yes |
| `PairedV2FullCertificateData` | [38680984398](https://github.com/UyNewNas/goldbach-formalization/actions/runs/38680984398) | 2 | yes |
| `PairedV2NaturalSumExpectedLengths` | [38680194674](https://github.com/UyNewNas/goldbach-formalization/actions/runs/38680194674) | 2 | yes |
| `PairedV2NaturalSumLengthsBlock11` | [38680194674](https://github.com/UyNewNas/goldbach-formalization/actions/runs/38680194674) | 1 | yes |
| `PairedV2NaturalSumLengthsBlock10` | [38680194674](https://github.com/UyNewNas/goldbach-formalization/actions/runs/38680194674) | 1 | yes |

The final four-module sum/partition/length/row bridge has nine declarations in run 38683648702, all with successful compilation, kernel replay, axiom audit and audit replay. It proves the actual 17,572-row numerator totals `55858378943374979` and `55858409959907296`, at the original common denominator `10^20`.

The twelve numerical sum blocks and generic Rows also have historical fully audited leaf records in runs 38674170679 and 38675247085. Those local per-module index entries do not embed the source hashes, so this audit records their existence without claiming an exact current object binding. All twelve data blocks were used as compiled prerequisites; that is not evidence of separate complete declaration/axiom audits for each data block.

## Confirmed original strip pilot failure

[Run 38692332902](https://github.com/UyNewNas/goldbach-formalization/actions/runs/38692332902), job `116280887851`, is completed/failure. The local `active-run.json` still says IN_PROGRESS, but the live run ended on 15 October 2026. AssemblyCore compiled (2.373 s) and passed leanchecker (4.78 s). Block00 compiled under `-t0 -j2 -M4096 -DwarningAsError=true` for 113.053 s and exited **-6**; the complete declaration and axiom audit was not reached.

The original compiler-log SHA-256 is `48bc2200174632932b9ea98fd0a0c30e6dc353ce535531045f1c7efc7b79940a`. The fetched job log only prints the stage receipt. It does not reveal the exact Lean line, memory-exception subtype or kernel/interpreter stage; this audit does not classify the exit further.

## Object availability

A bounded read-only filename search across `/workspace/scratch` and `/workspace/shared`, including hidden cache paths, found no PairedV2 `.olean`/`.ilean` or the selected child-8 semantic module objects. Root separately checked `/workspace/goldbach-p2/.lake` and `/workspace/p2-private-20261124/.lake` and reported no `PairedV2*.olean`. Root therefore began rebuilding necessary missing prerequisite objects. Historical proof acceptance is preserved; absent usable objects are a reconstruction issue, not a reason to rewrite already existing proofs. Unavailable remote artifact payloads were not exhaustively searched.

## Existing downstream sources and remaining boundary

- `ImbalancedChen/Certificates/P2AdoptedRowsActualEnclosure.lean`: existing implementation; no new acceptance found in the inspected verification collections.
- `ImbalancedChen/P2AdoptedRowsActualEnclosure.lean`: existing implementation; no new acceptance found in the inspected verification collections.
- `ImbalancedChen/Certificates/P2AdoptedUnionIntegral.lean`: existing implementation; no new acceptance found in the inspected verification collections.
- `ImbalancedChen/Certificates/P2PairedSupportFubini.lean`: existing implementation; no new acceptance found in the inspected verification collections.
- `ImbalancedChen/Certificates/P2ContinuousFibreFubini.lean`: existing implementation; no new acceptance found in the inspected verification collections.
- `ImbalancedChen/P2HistoricalFibreBinding.lean`: existing implementation; no new acceptance found in the inspected verification collections.
- `ImbalancedChen/P2PairedFibreBuchstabVariableLower.lean`: existing implementation; no new acceptance found in the inspected verification collections.
- `ImbalancedChen/P2PairedSemanticGainEnclosure.lean`: existing implementation; no new acceptance found in the inspected verification collections.
- `ImbalancedChen/Certificates/P2SemanticGainSetIntegral.lean`: existing implementation; no new acceptance found in the inspected verification collections.

`PairedV2FullCertificate.lean` already provides `all_certificates_checked`, rational `lower_sum`/`upper_sum`, `integral_bounds`, and `adopted_extra_gross_lower`. Its source remains listed as unaccepted until the full strip chain is verified.

The two `P2AdoptedRowsActualEnclosure.lean` files (top level and `Certificates/`) are byte-identical and define the same namespace/declarations. Their broad continuation entry points import different copies. Select one defining-module owner in the current acceptance closure.

The analytic chain does not discharge the separate P5 injection into the retained arithmetic parent or the historical-domain/five-to-four-coordinate counting correspondence. Source-matched historical leaves also do not establish a fresh whole-closure dependency/object audit.

## Evidence locations

All paths in the JSON are repository-relative historical evidence paths. The sparse P2.7 checkout may not materialize these paths; they were read from the existing P2 checkout at the same base commit. Main evidence:

- `automation/parts/p0/runs/20261015T060713Z-p2-sums-p1-coarse/terminal-and-acceptance-index.json`
- `automation/parts/p0/runs/20261015T042054Z-p2-p5-assembly/terminal-and-acceptance-index.json`
- `automation/parts/p0/runs/20261015T041100Z-p2-length-pilot/acceptance.json`
- `automation/parts/p0/runs/20261015T030155Z-p2-p4-finite/acceptance.json`
- `automation/parts/p0/runs/20261015T031200Z-p2-remainder/acceptance-index.json`
- `verification/parts/p2/DATA_SPLIT.md` and `STRIP_SPLIT.md`
- `verification/proof-continuation/2026-10-15/unaccepted-candidates.json`
