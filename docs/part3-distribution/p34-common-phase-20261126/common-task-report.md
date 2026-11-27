# P3.4 common-phase source unit

The source unit is committed and the focused P3 gate passed. Source commit `89fb011ec7f086621170b5bee819d1cf1230290e`, tree `41a780dc896aa5ebf77506f51f30fd0c72cac7d6`. The worktree was clean after the commit and exact-source check.

The edit base is `dc2aeb2e2f7e154d84ca7e258fa9461eef373923`. All three donor files have identical bytes at acceptance baseline `b945f39a1e355ff4fcca9865ab59ffc97f2172c0`. Before editing, `python .lake/p34-common-phase-preflight/source-check.py record` matched all five source blocks against the exact quotations in `NEXT_SCOPE_AUDIT.md`. It compared the three proof blocks and five retained actual-mode statements and proofs directly to the historical donor blobs.

Two normalized digests in the audit report include a trailing standalone section `end`. The audit's beta-assembly hash covers lines 62–83, and its final retained coprimality hash covers lines 72–80. The ledger hashes the actual declaration slices, lines 62–81 and 72–78, respectively. The current source, historical source and quoted exact blocks agree byte-for-byte. This is a source range discrepancy. The frozen manuscript lines 700–727 require keeping the original common factor and furnish no reason for a mathematical change.

The new provider imports pinned Mathlib trigonometric and natural finite-interval modules. The consumer imports only the common provider and the nine-module closure's assembly terminal. All original namespaces, names, hypotheses, statements, bodies, documentation and five retained actual-mode blocks are copied exactly. The donors retain their other bytes after the recorded removals and one added leading import per file.

The new verifier uses the existing shared runner. The Lean auditor differs from the previous auditor only by the two additional imports and module names. The accepted nine project source files, shared runner, pins and all prior evidence remain byte-identical. The three heavy parents and P3.1 joint import are outside this verification scope.

## Focused commands and preliminary results

All work was run from `/workspace/library-files/p34-proof-work`. The shell sourced `/workspace/library-files/p34-runtime/env.sh`. `lean --version` reported Lean 4.33.0-rc1, commit `62eed1db4d67327ec8120be05f1a1b0847d74561`. For direct focused checks, `LEAN_PATH` came from the previous accepted dyadic report's `tool_paths.lean_path`. All nine reused project object SHA-256 values matched that report.

- `lake env lean -t0 -j1 -M6000 -DwarningAsError=true .lake/p34-common-phase-preflight/before.lean` exited 1 with the five expected unknown identifiers under the old assembly import. The new consumer import separately exited 1 before relocation because its object was absent.
- The provider's `lean -t0 -j1 -M6000 -DwarningAsError=true -o .lake/build/lib/lean/ImbalancedChen/Part3CommonCompletedVariableCore.olean ImbalancedChen/Part3CommonCompletedVariableCore.lean` exited 0, emitted no diagnostics and produced SHA-256 `ec888fa55279d0959a0010fa653ff76b97bbe1b5f9d20e2620b4fb3d8fb0a459`.
- The first consumer strict process and a redundant direct baseline probe were killed simultaneously by the OS without Lean diagnostics. The Lake baseline probe had already furnished the expected result. The focused retry runs consumer strict and the joint auditor sequentially without overlapping local Lean processes.

The consumer retry was stopped intentionally at the coordinator's instruction after roughly four minutes with zero Lean diagnostics or consumer object. The retry command session exited 130. The two earlier OS-killed shell wrappers exited 1 and each printed a Bash `Killed` diagnostic. These are resource and cancellation events. They provide no Lean proof-failure evidence.

The seven implementation files were frozen while the coordinator ran the focused two strict compiles and the complete 11-module inventory in P3 with the nine accepted objects. The final exact-commit check is coordinator-owned and runs once for the encompassing 14-module union. The new 11-module entry point remains available.

The frozen source patch is `.lake/p34-common-phase-preflight/frozen-source.patch`, SHA-256 `306b384bf7d17f1e4ceaf27dc4c0d96974cc7bb3b10dd81ab6d719b7e6d0d969`. The source-only ledger staging file is `.lake/p34-common-phase-preflight/source-only-ledger.json`. It records all exact source/target blocks, old donor identities and retained remainders. The compiler fields in the committed ledger come from completed P3 focused task `d89a6e0e760041ccbf72888c17ee6552`.


## P3 focused verification

The complete evidence is in `/workspace/library-files/p34-evidence-staging/common-focused-cloud`. The bundle `focused-evidence.zip` has SHA-256 `619a3d5cb3b08a068ce68dc10cd9a6f80b804064dc25478e9086e4a490133968`. The receipt reports `FOCUSED_PASSED` with the following exit statuses.

| Stage | Exit | Seconds |
| --- | ---: | ---: |
| Provider resolved imports | 0 | 2.909 |
| Provider strict compile | 0 | 2.813 |
| Provider bundled leanchecker replay | 0 | 5.819 |
| Consumer resolved imports | 0 | 0.711 |
| Consumer strict compile | 0 | 3.405 |
| Consumer bundled leanchecker replay | 0 | 6.387 |
| Auditor resolved imports | 0 | 0.782 |
| Complete Lean owner, type and transitive axiom audit | 0 | 60.259 |

The exact stage commands and object digests are in the focused `report.json`. Each new module used `lake env lean --deps`, then `lake env lean -t0 -j1 -M6000 -DwarningAsError=true -o <olean> <source>` and bundled `leanchecker --verbose`. The auditor used `lake env lean --deps verification/P34CommonPhaseAudit.lean` and `lake env lean -t0 -j1 -M6000 -DwarningAsError=true verification/P34CommonPhaseAudit.lean`. I recomputed all 15 focused source/pin digests directly from the committed Git blobs and matched all nine imported object digests against the earlier accepted local dyadic report.

The complete inventory contains 192 declarations across 11 modules. All 168 prior owner, type and axiom records match exactly. The new provider owns 20 and the new consumer owns 4, comprising the five public moves and 19 generated constants. The common consumer's generated `ImbalancedChen.P3ZActualPrimaryShortEndpoint.dyadicPacket.congr_simp` and the provider's `CommonCompletedVariable.weight._proof_1` are enumerated in the ledger. The complete inventory has no `CommonCompletedVariable.weight.eq_1`. Its transitive axioms are within `propext`, `Classical.choice` and `Quot.sound`, and the Lean audit found equal serialized and actual-owner inventories. There were zero proof repairs.

## Source and ledger self-review

I matched each source block including its leading documentation and final LF against the quoted audit and exact donor commit. Historical blobs independently supply the same three proof and five retained declaration blocks. The original interval remains half-open, the phase remains real, and the original complex exponential is unchanged. The short theorem retains the independent sign parameter and both branches of membership at 1. Both assembly proofs preserve the exact complex payload and the position of the common weight. The new proof blocks contain no explicit unfolding of the common weight.

The source check script's `ledger <axioms.log>` mode used the shared inventory validator for the raw complete audit. The `verify <declarations.json>` mode regenerated all move, owner, type, axiom and remainder fields byte-for-byte from the structured evidence. `verify-sources` confirmed that all five Lean files and two verifier files matched the frozen staging bytes. The committed ledger SHA-256 is `adb3f5ecacaf64d9b7700747a2c2e2ddee64b49cc50bb48d47d53c98b23363d4`.

`git diff --cached --check` and the pre-commit unstaged diff check exited 0. The commit contains exactly the two new Lean modules, three old donor import/removal edits, verifier, auditor and ledger. The following exact-commit command passed `head`, `working-tree` and `baseline-ancestor`, and bound 20 source and configuration files.

```bash
python verification/verify_p34_common_phase.py --source-only --expected-head 89fb011ec7f086621170b5bee819d1cf1230290e --output-dir .lake/p34-common-phase-preflight/exact-source-only
```

The finished evidence consists of focused strict compilation and replay for the two new owners, joint inventory with nine hash-bound previously accepted objects, and an exact clean-commit source-only check. The coordinator's fresh full 14-module gate is pending. The heavy parent files, P3.1 joint import and broader P3.4 remain outside the focused gate.
