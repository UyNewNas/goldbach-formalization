# Cell05 repaired Shape executor

The root P2 operator deploys four regular files into an isolated stage on the persistent original P2 host. Historical inputs remain at their original absolute paths. The repaired source was authored locally. The Lean owned-declaration audit is the unchanged 2,720-byte audit from the original frozen verifier.

Stage root is `/workspace/p26-cell05-shape-completion-20261127-v1`. In the table, `tools` abbreviates `tools/p26/cell05-shape-completion-20261127`. Copy the two Python/configuration inputs and audit from the directory containing this document. Copy the source from `materials/p26-work/ImbalancedChen`. Verify all four destination sizes and SHA-256 digests before starting the interpreter. Use exclusive creation or require identical existing bytes. Preserve any prior output on a mismatch.

| Stage member | Bytes | SHA-256 |
|---|---:|---|
| tools/complete_shape.py | 36421 | 6b98383da4825d2e6c4074cea08302bb4e3b47b3d183614f648126aa1bda53db |
| tools/PINS.json | 25524 | be4fc8f2064e9ba988a8eaed42b54831635eca9a297abf57bd08c08446b5be86 |
| tools/owned-audits/P2OriginalSaving19Geometry05ScalableShape.lean | 2720 | e5106b4fcb2f8c166a26e9888e23e54b5435deb4dee50f89e27a7877bda43fd1 |
| project/ImbalancedChen/P2OriginalSaving19Geometry05ScalableShape.lean | 7508 | fd381d234ea1c9100d9248542273663df8b3042282326410a9fe8aaf961d90bb |

## Root operator commands

Run each invocation in a serial P2 job with memory 13,107 MiB and wall time 3,600 seconds. The executor enforces a process-tree RSS cap of 12 GiB and a wall limit of 900 seconds per proof command. A normal run uses one thread.

```sh
driver=/workspace/p26-cell05-shape-completion-20261127-v1/tools/p26/cell05-shape-completion-20261127/complete_shape.py
python3 -I -B "$driver" preflight
python3 -I -B "$driver" run
```

The first invocation checks the original 9-owner package, 117-supplier evidence join, raw 8-owner prefix and ninth-owner failure. It validates the repaired source and unchanged audit. It installs regular copies of 125 selected source/object pairs directly into the new project and object roots. It writes `PREFIX8_VALIDATED.json` and `verification/RUN.json`. No proof process is launched during preflight.

The second invocation rederives the frozen context then runs each missing mode in order. The individual operations `normal`, `kernel` and `owned` allow separate serial jobs. Calling an already accepted mode rechecks its chain without launching it. The `verify` operation requires the existing SUCCESS, combined index and archive. It rechecks all three accepted modes and their durable launch witnesses, compares both published summaries, and rereads the archive against the member manifest. Its success status is `RETAINED_EVIDENCE_VERIFIED`. The `run` operation handles final publication after the third mode. An interrupted or failed step blocks further execution at the affected stage. Preserve all files, including unsealed evidence and any partial archive. The driver's SSH or shell caller need not set any Lean environment variables.

## Produced evidence

- `PREFIX8_VALIDATED.json` links the unchanged pilot and continuation stops, all 113 raw file pins, the 24 accepted seals and the failed normal command, log, result and source. The recorded recovered archive SHA-256 is `e556b30c03235d395c2a90fbb3daf213e22806fa4bdf2520d7ddfc8821aaa2a4`.
- `launch-witnesses/{normal,kernel,owned}.json` contains independent per-mode records bound to the RUN and exact command. Their file and directory entries are flushed to disk before launch. An orphaned, mismatching or missing witness blocks replay. All three witnesses are archived.
- `verification/{normal,kernel,owned}-command.json`, `*.log`, `*-result.json` and `*-accepted.json` link to the single-owner RUN. The owned result links the complete parsed `owned-declarations.json` and the raw log.
- `verification/SUCCESS.json` covers one repaired owner and three commands. `COMBINED_INDEX.json` points to the historical 24 and separately accepted three. Both retain the Cell05 parse/decode/finite-shape scope with `P2_6_complete=false`.
- `exports/shape-evidence.tar.xz` contains these receipts, script/configuration, the repaired source and object, and the owned audit. Its manifest binds all archive members. The old 125 supplier object bodies are excluded. The final command prints the archive path, size and SHA-256.

## Local review

Nine isolated unit tests passed with `python3 -I -B test_complete_shape.py -v`. They check strict argv and checker selection, reject a changed source or undeclared object, preserve incomplete successful receipts, refuse replay after receipt loss with a retained archive, reject forbidden axioms and missing prints, reject a wrong import closure, reject changed RUN/argv even when receipt links are updated, and exercise a two-mode no-replay sequence with a synthetic process result. Local bootstrap also authenticated all original verifier workflow files and matched all 113 archived raw receipt pins.

The tests execute no Lean commands and cannot attest live P2 filesystem metadata, runtime guard continuity, actual compiler output or formal acceptance. Resource reporting uses the inherited sampled process-tree RSS at 100 ms intervals. Interrupted steps with ambiguous execution deliberately require evidence recovery. The P2 root remains responsible for the live preflight, three proof commands and archive preservation.


## Independent review fixes, round 1

| Finding | Implementation | Local regression |
|---|---|---|
| R1. Child Python imports | The driver authenticates remaining9, prefix13 and shape1 code directories against their pinned manifests before importing the remaining9 helpers or running the probes. It holds shared nonblocking origin execution locks and rescans the directories after successful validation. Both child families retain their original isolated Python commands. It checks the directory containing the explicit prefix-validator source loader as well as both child import roots. | An isolated interpreter runs the actual frozen origin-probe entrypoint with `--help` on a clean fixture. Adding an inert cache file at the prefix-validator entrypoint, a bytecode or extension candidate, an unknown package or a loose Python source in either child family prevents launch. |
| R2. Trailing receipt loss | Each proof process requires an exclusively created, separately located launch witness. Before spawn, the driver fsyncs the RUN, command and witness, then the receipt, witness and stage directories. Every resumed mode reconciles these files with the three-mode prefix. Results and seals include the witness fingerprint. | A simulated normal/kernel sequence remains resumable. Losing all four kernel receipt files after its launch, losing its witness, and substituting either witness link each block execution. The suffix-loss test asserts zero additional process launches. |
| R3. Read-only verification | `verify` requires previously published SUCCESS, combined index and archive before opening the stage. It only reads the summaries and calls the generic member-by-member archive reader. | Removing each final artifact leaves all other bytes untouched. A successful synthetic three-mode archive verifies without invoking the archive writer. An altered retained index fails and keeps its altered bytes. |

The reviewed pre-fix driver, tests and deployment notes are preserved under `review/round-1/before/`. The unified changes are in `review/round-1/fix.diff`, the captured test output is in `review/round-1/test-output.txt`, and exact file pins are in `review/round-1/fix-report.json`. These files are local review material. Deploy only the four members in the table above.

From the shared scratch root, the exact round-1 test command was

```sh
D=materials/p26-work/tools/p26/cell05-shape-completion-20261127
python -I -B "$D/test_complete_shape.py" -v > "$D/review/round-1/test-output.txt" 2>&1
```

The captured run ended with `Ran 14 tests in 0.430s` and `OK`. The printed process metrics, seals and archive in this simulation are unit-test fixtures. The original runtime guard remains a precondition for every live proof command. The root operator separately observed that the guard rejected the current P2 Mathlib inventory. These code changes do not establish live runtime continuity or formal acceptance.
