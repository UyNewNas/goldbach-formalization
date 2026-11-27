# Cell05 repaired Shape executor

The root P2 operator deploys four regular files into an isolated stage on the persistent original P2 host. Historical inputs remain at their original absolute paths. The repaired source was authored locally. The Lean owned-declaration audit is the unchanged 2,720-byte audit from the original frozen verifier.

Stage root is `/workspace/p26-cell05-shape-completion-20261127-v1`. In the table, `tools` abbreviates `tools/p26/cell05-shape-completion-20261127`. Copy the two Python/configuration inputs and audit from the directory containing this document. Copy the source from `materials/p26-work/ImbalancedChen`. Verify all four destination sizes and SHA-256 digests before starting the interpreter. Use exclusive creation or require identical existing bytes. Preserve any prior output on a mismatch.

| Stage member | Bytes | SHA-256 |
|---|---:|---|
| tools/complete_shape.py | 30884 | 05d5fb383cf8861d03790f2920f5bcaf4882c8dd06a12f6f63a54ac8e3f1e2fb |
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

The second invocation rederives the frozen context then runs each missing mode in order. The individual operations `normal`, `kernel` and `owned` allow separate serial jobs. Calling an already accepted mode rechecks its chain without launching it. The `verify` operation rechecks all three accepted modes and the archive. An interrupted or failed step blocks further execution at the affected stage. Preserve all files, including unsealed evidence and any partial archive. The driver's SSH or shell caller need not set any Lean environment variables.

## Produced evidence

- `PREFIX8_VALIDATED.json` links the unchanged pilot and continuation stops, all 113 raw file pins, the 24 accepted seals and the failed normal command, log, result and source. The recorded recovered archive SHA-256 is `e556b30c03235d395c2a90fbb3daf213e22806fa4bdf2520d7ddfc8821aaa2a4`.
- `verification/{normal,kernel,owned}-command.json`, `*.log`, `*-result.json` and `*-accepted.json` link to the single-owner RUN. The owned result links the complete parsed `owned-declarations.json` and the raw log.
- `verification/SUCCESS.json` covers one repaired owner and three commands. `COMBINED_INDEX.json` points to the historical 24 and separately accepted three. Both retain the Cell05 parse/decode/finite-shape scope with `P2_6_complete=false`.
- `exports/shape-evidence.tar.xz` contains these receipts, script/configuration, the repaired source and object, and the owned audit. Its manifest binds all archive members. The old 125 supplier object bodies are excluded. The final command prints the archive path, size and SHA-256.

## Local review

Nine isolated unit tests passed with `python3 -I -B test_complete_shape.py -v`. They check strict argv and checker selection, reject a changed source or undeclared object, preserve incomplete successful receipts, refuse replay after receipt loss with a retained archive, reject forbidden axioms and missing prints, reject a wrong import closure, reject changed RUN/argv even when receipt links are updated, and exercise a two-mode no-replay sequence with a synthetic process result. Local bootstrap also authenticated all original verifier workflow files and matched all 113 archived raw receipt pins.

The tests execute no Lean commands and cannot attest live P2 filesystem metadata, runtime guard continuity, actual compiler output or formal acceptance. Resource reporting uses the inherited sampled process-tree RSS at 100 ms intervals. Interrupted steps with ambiguous execution deliberately require evidence recovery. The P2 root remains responsible for the live preflight, three proof commands and archive preservation.
