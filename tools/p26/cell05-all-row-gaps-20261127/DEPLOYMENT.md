# Cell05 AllRowGaps execution contract

## Fixed scope

This package has one new owner, `ImbalancedChen.P2OriginalSaving19Cell05AllRowGaps`. It reuses 128 existing suppliers: the accepted Shape module and its 125 suppliers, plus the canonical RowNumericsPure and Q96ArithmeticPure modules. The complete project import closure is 129 modules. Successful execution requires exactly three new checks: normal compilation, stock kernel replay of the same object, and complete module-owned declaration auditing.

The source proves positive gap sums and the stored mean-gap equality for all 56 concrete Cell05 geometry rows: clauses 3 and 5 of `RowDataChecksFor`. This is zero newly complete ten-clause rows and zero newly Archive-bound rows. `P2_6_complete` remains false. Twenty explicit axiom prints are not an owned declaration count; the actual serialized/environment inventory controls the latter, including private and generated declarations.

## Frozen authorities

`WORKFLOW_MANIFEST.json` pins every file in this workflow package. Its independently supplied SHA256 is the CLI trust anchor. `CONFIG.json` pins the new source and audit, the pure2 transport, the exact accepted Shape driver/configuration/RUN/SUCCESS/index/archive/recovery binding, and the original runtime compatibility document. Each process verifies these bodies. Pinned predecessor sources are executed from the same cached bytes that were hashed, without importing bytecode or substituting constants.

The old Shape driver is invoked only through a fresh isolated worker selecting its original `verify` action. That unchanged read-only action verifies its three accepted command/result/log/seal chains, nested predecessor authorities, original recovery-v2 protocol and current runtime guard. It does not replay Lean or the kernel. The original old guard remains unchanged and is not claimed to pass its physical file checks. The newer recovery certificate and current guard remain explicit, separate authorities.

The two pure suppliers retain their original normal/kernel commands and four result/log chains, including their original `local_fixture_path_not_P1` status. Their old normal commands did not contain explicit trust-zero or warning-as-error flags. This workflow does not rewrite those historical claims or add an independent old owned audit requirement. It joins the source/object bytes, original MANIFEST/AUDIT/RUNTIME, original closure receipt pointers and shared dependency pins. Current compatibility is tied to the accepted full ten-root byte comparison and current recovery guard; no historical loaded inventory is invented.

## Deployment inputs

Root deploys only after independent review. Do not modify old stages or clear the new stage. The existing pure2 deployment already occupies the authorized input paths.

| Destination under `/workspace/p26-cell05-all-row-gaps-20261127-v1` | Required content |
|---|---|
| `tools/p26/cell05-all-row-gaps-20261127/` | Exactly the manifest and its listed workflow payloads, including the unchanged owned audit |
| `project/ImbalancedChen/P2OriginalSaving19Cell05AllRowGaps.lean` | Source pinned by `CONFIG.json` |
| `inputs/pure2/` | The 17-member capsule pinned through its `TRANSPORT.json` |
| `inputs/pure2-original-evidence.tar.xz` | Existing transport archive; retained as deployment evidence |
| `inputs/PURE2_DEPLOYMENT.json` | Existing deployment record; retained unchanged |

Source pin: 5,953 bytes, SHA256 `d6fea35ead2155c41b91368765e4983a6c960098a0d405e2045c556c8abf94f3`.

Audit pin: 2,706 bytes, SHA256 `9498aafa82b33b348ab622ebe98959f31363caca32a0ff6926e7cfc0ec53ea20`.

Pure2 archive pin: 266,236 bytes, SHA256 `874cf979a761f81d76761b937e76c81d6ee635244e734285280a79e949840960`. Its extracted `TRANSPORT.json` is 17,815 bytes, SHA256 `e4515252ec4bbc5f3066a8a5967ae384ab71ce6cbd181b0dd7bf6a221f43a4c3`.

The accepted predecessor must remain at `/workspace/p26-cell05-shape-completion-20261127-v1`, with its original remaining9 and recovery-v2 inputs available at their unchanged paths. The package does not deploy, replace, repair or reconstruct those inputs. Initial preflight creates ordinary independent copies of the 128 authenticated source/object pairs in the new `project` and `objects` trees. After RUN exists, missing copies cause rejection rather than reconstruction.

## Commands and results

Replace `MANIFEST_SHA256` with the reviewed SHA256 of `WORKFLOW_MANIFEST.json`. Use the same digest for every action. The Python command must use isolation and disable bytecode; the documented form additionally disables site initialization.

```sh
python3 -I -S -B /workspace/p26-cell05-all-row-gaps-20261127-v1/tools/p26/cell05-all-row-gaps-20261127/run_gaps.py preflight --workflow-sha256 MANIFEST_SHA256
python3 -I -S -B /workspace/p26-cell05-all-row-gaps-20261127-v1/tools/p26/cell05-all-row-gaps-20261127/run_gaps.py run --workflow-sha256 MANIFEST_SHA256
python3 -I -S -B /workspace/p26-cell05-all-row-gaps-20261127-v1/tools/p26/cell05-all-row-gaps-20261127/run_gaps.py verify --workflow-sha256 MANIFEST_SHA256
```

`preflight` performs no proof command and reports `PASS_PREFLIGHT`, `old_suppliers: 128`, `project_closure: 129` and the number of already accepted new steps. It freezes the new RUN and supplier reuse record, checks namespace closure and revalidates all old authorities. It does not mean the new owner passed.

`run` performs only the missing suffix of the three new modes. Alternatively select exactly `normal`, `kernel` or `owned` in place of `run`; prior modes must already be accepted. Selecting an accepted mode verifies its existing receipt and performs no new proof command. Every mode validates all frozen inputs before and after execution. Normal and owned use explicit `--trust=0 -DwarningAsError=true`, one thread, 12 GiB RSS limit and 900 seconds wall limit. Kernel uses the pinned stock checker with `--verbose` and the exact new module name.

Successful final publication reports `ALL_ROW_GAPS_SUCCESS`, pins for `success`, `reuse_index` and `archive`, `accepted_targets: 1`, `accepted_steps: 3`, `old_proof_commands: 0`, and `P2_6_complete: false`.

`verify` requires all retained output to exist, verifies it without writing or running any proof command, and reports the same output pins with status `RETAINED_EVIDENCE_VERIFIED`. It never recreates directories, supplier copies, summaries, missing receipts or archives. An original read-only Shape verification subprocess is expected during this action.

## Durability and retained evidence

Each new mode creates an exclusive command record and a separate `launch-witnesses/<mode>.json`. RUN, command, witness and their directories are fsynced before process launch. A surviving witness with missing command/result/log/seal blocks replay. Partial receipts, non-prefix receipts, orphan objects or owned inventories, and STOPPED stages also block further proof commands. Accepted prefixes are never overwritten.

New raw records are `verification/<mode>-command.json`, `<mode>.log`, `<mode>-result.json` and `<mode>-accepted.json`. The complete owned inventory is `verification/owned-declarations.json`; `owned-result.json` also retains the unique association between each original normal-print spelling and its actual complete-owned name. A failed completed command retains its raw result/log and `STOPPED.json`. An interrupted launch retains its durable witness and any partial files; it must be reviewed without replay or deletion.

Final outputs are `verification/SUCCESS.json`, `REUSE_INDEX.json` and `exports/gaps-evidence.tar.xz`. The archive includes the new source/object/audit, all new raw evidence and witnesses, this entire workflow package, all 17 pure2 capsule files, the supplier reuse record, and the exact predecessor driver/configuration/RUN/SUCCESS/index/binding/archive under `predecessor/`. The nested predecessor archive preserves its original chains and recovery evidence. The archive does not bulk-copy the other 125 supplier objects. Live verification still requires the original pinned source/object paths and the accepted current guard; the export does not claim to be a standalone replacement runtime.

## Local verification boundary

The author tests use exact original pure2 metadata and frozen helper code, plus harmless local fixtures for new process effects. They cover metadata tampering, same-name supplier conflicts, strict argv, complete generated/private inventory handling, unique private aliases, prefix resume, durable suffix-loss rejection, altered commands, retained post-launch failure, read-only verification, archive recheck and isolated worker authentication. They do not execute Lean or prove this owner. `TEST_RESULTS.json` binds the actual local test command/output; the cloud three-chain result and independent readback are separate required gates.
