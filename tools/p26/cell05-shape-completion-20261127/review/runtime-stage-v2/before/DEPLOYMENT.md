# Cell05 repaired Shape executor

The root P2 operator deploys four fixed files and one capture-specific binding file into an isolated stage on the persistent original P2 host. Historical inputs remain at their original absolute paths. The repaired source was authored locally. The Lean owned-declaration audit is the unchanged 2,720-byte audit from the original frozen verifier.

Stage root is `/workspace/p26-cell05-shape-completion-20261127-v1`. In the table, `tools` abbreviates `tools/p26/cell05-shape-completion-20261127`. Copy the two Python/configuration inputs and audit from the directory containing this document. Copy the source from `materials/p26-work/ImbalancedChen`. Verify all four destination sizes and SHA-256 digests before starting the interpreter. Use exclusive creation or require identical existing bytes. Preserve any prior output on a mismatch.

| Stage member | Bytes | SHA-256 |
|---|---:|---|
| tools/complete_shape.py | 45345 | 50416aba871b79b6ddcc54af8264c8ee76cc018d08ad79726f52dc2d52fe6151 |
| tools/PINS.json | 25524 | be4fc8f2064e9ba988a8eaed42b54831635eca9a297abf57bd08c08446b5be86 |
| tools/owned-audits/P2OriginalSaving19Geometry05ScalableShape.lean | 2720 | e5106b4fcb2f8c166a26e9888e23e54b5435deb4dee50f89e27a7877bda43fd1 |
| project/ImbalancedChen/P2OriginalSaving19Geometry05ScalableShape.lean | 7508 | fd381d234ea1c9100d9248542273663df8b3042282326410a9fe8aaf961d90bb |
| tools/RECOVERY_BINDING.json | From the retained capture | Operator-provided SHA-256 |

## Bind the independently reviewed recovery protocol

The inspected historical lstat guard rejected the changed P2 filesystem. The new RUN preserves its original fingerprint and explicitly records `original_live_guard_validator_passed=false`. The independent recovery protocol must complete its own review and authenticated live capture. It attests equality against the original ten-root runtime snapshot and supplies a fresh current guard. Shape's normal, kernel and owned commands all depend on this certificate.

Using the returned capture JSON, copy the full `certificate`, `current_runtime_guard`, and `history` identities into a fresh `RECOVERY_BINDING.json`. Set `protocol_manifest` from the **independently reviewed and deployed** protocol manifest identity, then compare it with the identity in the capture. Each identity has the exact absolute path, positive byte count and SHA-256. The schema and expected fixed paths are in `RECOVERY_BINDING.example.json`. Its null placeholders deliberately fail validation. Keep the actual binding exclusively in the new Shape tool directory. Retain its size and SHA-256 alongside the trusted capture and deployment record.

Before each protocol subprocess, the driver verifies the binding against that operator-supplied SHA-256. It checks the real manifest and the exact bytes of every listed source and data file, requires the three executable modules and anchors, rejects additional import candidates, and verifies the three captured artifact identities. It starts only the separate protocol's read-only `verify` command in a fresh Python interpreter with `-I -S -B`, passing the bound certificate size and SHA-256. It authenticates those bytes again after the subprocess. Existing Shape RUNs must reference the identical binding.

## Root operator commands

Run each invocation in a serial P2 job with memory 13,107 MiB and wall time 3,600 seconds. The executor enforces a process-tree RSS cap of 12 GiB and a wall limit of 900 seconds per proof command. A normal run uses one thread.

```sh
driver=/workspace/p26-cell05-shape-completion-20261127-v1/tools/p26/cell05-shape-completion-20261127/complete_shape.py
# Set this value from the independently retained capture-binding record.
: "${SHAPE_RECOVERY_BINDING_SHA256:?supply the verified binding digest}"
python3 -I -B "$driver" preflight --recovery-binding-sha256 "$SHAPE_RECOVERY_BINDING_SHA256"
python3 -I -B "$driver" run --recovery-binding-sha256 "$SHAPE_RECOVERY_BINDING_SHA256"
```

The first invocation verifies the recovery certificate, including the original 117-supplier join. It then independently rechecks the pinned original package, all 24 accepted seals of its first eight targets, the genuine failed ninth-owner normal, and all 125 selected source/object pairs against the returned recovery view. It validates the repaired source and unchanged audit. It installs regular copies of 125 selected source/object pairs directly into the new project and object roots. It writes `PREFIX8_VALIDATED.json` and `verification/RUN.json`. No proof process is launched during preflight.

The second invocation rederives the frozen context then runs each missing mode in order. Every proof command and final export or retained-evidence verification rechecks the bound recovery certificate, full frozen evidence and current guard before and after execution. The individual operations `normal`, `kernel` and `owned` allow separate serial jobs. Calling an already accepted mode rechecks its chain without launching it. The `verify` operation requires the existing SUCCESS, combined index and archive. It rechecks all three accepted modes and their durable launch witnesses, compares both published summaries, and rereads the archive against the member manifest. Its success status is `RETAINED_EVIDENCE_VERIFIED`. The `run` operation handles final publication after the third mode. An interrupted or failed step blocks further execution at the affected stage. Preserve all files, including unsealed evidence and any partial archive. The driver's SSH or shell caller need not set any Lean environment variables.

## Produced evidence

- `PREFIX8_VALIDATED.json` links the unchanged pilot and continuation stops, all 113 raw file pins, the 24 accepted seals and the failed normal command, log, result and source. The recorded recovered archive SHA-256 is `e556b30c03235d395c2a90fbb3daf213e22806fa4bdf2520d7ddfc8821aaa2a4`.
- `launch-witnesses/{normal,kernel,owned}.json` contains independent per-mode records bound to the RUN and exact command. Their file and directory entries are flushed to disk before launch. An orphaned, mismatching or missing witness blocks replay. All three witnesses are archived.
- `verification/{normal,kernel,owned}-command.json`, `*.log`, `*-result.json` and `*-accepted.json` link to the single-owner RUN. The owned result links the complete parsed `owned-declarations.json` and the raw log.
- `verification/SUCCESS.json` covers one repaired owner and three commands. `COMBINED_INDEX.json` points to the historical 24 and separately accepted three. Both retain the Cell05 parse/decode/finite-shape scope with `P2_6_complete=false`.
- `exports/shape-evidence.tar.xz` contains these receipts, script/configuration, the repaired source and object, and the owned audit. Its manifest binds all archive members. The archive also includes the operator binding and the original bytes of the recovery certificate, historical validation, current guard, protocol manifest and every manifest member. These separate-stage files use archive member names under `recovery/`. The old 125 supplier object bodies are excluded. The final command prints the archive path, size and SHA-256.

## Runtime-recovery integration tests

Nineteen isolated local tests passed. The new contract tests compare the original successful-prefix records, failed chain and supplier source/object paths, reject a protocol source change before subprocess creation, reject capture/view discrepancies, and check the exact recovery artifact bytes in the synthetic final archive. The real recovery executable, live capture and Lean were not run in these tests. The complete pre-integration files, changes, test output and hashes are under `review/runtime-integration/`.

## Earlier local reviews of the historical-guard driver

The following entries describe the pre-integration versions. The capture binding and current invocation instructions above supersede their old runtime precondition and four-file deployment instructions.

Nine isolated unit tests passed with `python3 -I -B test_complete_shape.py -v`. They check strict argv and checker selection, reject a changed source or undeclared object, preserve incomplete successful receipts, refuse replay after receipt loss with a retained archive, reject forbidden axioms and missing prints, reject a wrong import closure, reject changed RUN/argv even when receipt links are updated, and exercise a two-mode no-replay sequence with a synthetic process result. Local bootstrap also authenticated all original verifier workflow files and matched all 113 archived raw receipt pins.

The tests execute no Lean commands and cannot attest live P2 filesystem metadata, runtime guard continuity, actual compiler output or formal acceptance. Resource reporting uses the inherited sampled process-tree RSS at 100 ms intervals. Interrupted steps with ambiguous execution deliberately require evidence recovery. The P2 root remains responsible for the live preflight, three proof commands and archive preservation.


## Independent review fixes, round 1

| Finding | Implementation | Local regression |
|---|---|---|
| R1. Child Python imports | The driver authenticates remaining9, prefix13 and shape1 code directories against their pinned manifests before importing the remaining9 helpers or running the probes. It holds shared nonblocking origin execution locks and rescans the directories after successful validation. Both child families retain their original isolated Python commands. It checks the directory containing the explicit prefix-validator source loader as well as both child import roots. | An isolated interpreter runs the actual frozen origin-probe entrypoint with `--help` on a clean fixture. Adding an inert cache file at the prefix-validator entrypoint, a bytecode or extension candidate, an unknown package or a loose Python source in either child family prevents launch. |
| R2. Trailing receipt loss | Each proof process requires an exclusively created, separately located launch witness. Before spawn, the driver fsyncs the RUN, command and witness, then the receipt, witness and stage directories. Every resumed mode reconciles these files with the three-mode prefix. Results and seals include the witness fingerprint. | A simulated normal/kernel sequence remains resumable. Losing all four kernel receipt files after its launch, losing its witness, and substituting either witness link each block execution. The suffix-loss test asserts zero additional process launches. |
| R3. Read-only verification | `verify` requires previously published SUCCESS, combined index and archive before opening the stage. It only reads the summaries and calls the generic member-by-member archive reader. | Removing each final artifact leaves all other bytes untouched. A successful synthetic three-mode archive verifies without invoking the archive writer. An altered retained index fails and keeps its altered bytes. |

The reviewed pre-fix driver, tests and deployment notes are preserved under `review/round-1/before/`. The unified changes are in `review/round-1/fix.diff`, the captured test output is in `review/round-1/test-output.txt`, and exact file pins are in `review/round-1/fix-report.json`. These files are local review material from the earlier four-file driver.

From the shared scratch root, the exact round-1 test command was

```sh
D=materials/p26-work/tools/p26/cell05-shape-completion-20261127
python -I -B "$D/test_complete_shape.py" -v > "$D/review/round-1/test-output.txt" 2>&1
```

The captured run ended with `Ran 14 tests in 0.430s` and `OK`. The printed process metrics, seals and archive in this simulation are unit-test fixtures. At that revision, the original runtime guard was a precondition for every live proof command. The root operator separately observed that the guard rejected the current P2 Mathlib inventory. These code changes do not establish live runtime continuity or formal acceptance.

## Independent review fixes, round 2

The scoped round-1 reviewer passed R1 and R2 and requested an entrypoint correction to R3. During `verify`, the driver now opens the existing execution locks read-only and requires the object namespace and verification directory to exist. The common preparation path can no longer create a missing object directory during this action.

A new test invokes the real `main()` with an isolated temporary stage. It substitutes fixture data for historical bootstrap only and compares all directory entries and file contents before and after the failed verification. Its five cases remove the entire object tree, its project namespace, the verification tree, the new stage lock, or the historical lock. It also rejects writable file-open modes and checks that neither lock is recreated and no proof process starts.

From the shared scratch root, the exact commands were

```sh
D=materials/p26-work/tools/p26/cell05-shape-completion-20261127
python -I -B "$D/test_complete_shape.py" -v > "$D/review/round-2/test-output.txt" 2>&1
python -I -B "$D/test_complete_shape.py" ReceiptBoundary.test_verify_main_preserves_damaged_directories_and_opens_existing_locks_readonly -v > "$D/review/round-2/targeted-output.txt" 2>&1
```

The full suite reported `Ran 15 tests in 0.423s` and `OK`. The focused test passed all five subcases. Pre-fix files, both command outputs, the unified diff and exact hashes are under `review/round-2/`. This round covers local audit tooling only. At that revision, the historical runtime guard was required for live proof execution.
