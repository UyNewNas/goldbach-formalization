# SDD ledger — plan: docs/plans/20261127-cell05-shape-completion.md

## Recovery and implementation state

- Remote base46d7a9b20373700d7e862116344abfb28243289f. Local partial authoring snapshot baselineb8c132e8bbb0b4654e9a39ca3b0c49e8c3d498d1; do not push this partial history as a full remote repository.
- Exact original remaining9 snapshot403524bytes SHA e556b30c03235d395c2a90fbb3daf213e22806fa4bdf2520d7ddfc8821aaa2a4,198members. Recovered8 owners/24accepted steps and original failed Shape normal. Raw-chain validation job d8ffb8f12c9c49e69e87d3119e9b1ef7 failed at the original runtime lstat guard; original document bytes still match.
- Task1: source repair written, static spec+quality review PASS by /root/p26_remote_audit, actual Lean checks pending. Source SHA fd381d234ea1c9100d9248542273663df8b3042282326410a9fe8aaf961d90bb.
- Task2: implementer /root/shape_completion_runner owns tools/p26/cell05-shape-completion-20261127; testing in progress. No cloud deployment yet.
- Task3: pending root independent review, deployment, strict3checks, full evidence readback and publication.

## Interface/conflict scan

| Tasks/interface | Producer and consumer | Finding/ruling |
|---|---|---|
| Task1 internal | Six proof terms, unchanged statements | Static independent review PASS; require actual regression closure in Task3. |
| Task2 internal | Exact old validators and fresh one-owner workflow | Old9/27 SUCCESS helpers cannot validate8/24; use raw original prefix primitives and independent schema. |
| Task3 internal | Exact bytes, real cloud outcomes, accurate publication | Gate acceptance on raw outputs, not queue submission or source preparation. |
| Task1 → Task2 | Repaired Lean7508bytes + unchanged owned audit | Bind exact SHA in PINS; reject changes. |
| Task2 → Task3 | Frozen executor/config/audit; structured receipts | Review before deployment and compare final pins, new stage one owner only. |
| Task1 → Task3 | Complete declaration types and unchanged semantics | Strict normal/stock kernel/full-owned, declared-module scope126. |

Ruling: preserve original24-step evidence and failed9-target context without changing its counts or source — exact recovery is required; inventing aggregate old SUCCESS would misrepresent history.

Ruling: author in this isolated partial git workspace and publish explicit paths onto the actual remote base by lease — full checkout is unavailable locally and overwriting the repository from a partial tree would be wrong.

Ruling: new commands explicitly use --trust=0 and -DwarningAsError=true; retain old argv exactly — the pinned Lean shell default is maximal trust, so historical commands must not be described as explicitly trust0.

Ruling: ongoing authorization covers continuation and existing work-branch checkpoint pushes; no further permission prompt is needed for these reversible task actions. Full P2.6 is not declared closed.

- Task 2: fix round 1/5 (R1 and R2 addressed; R3.1 remains open — verify creates missing directories before failing; source-only reviewed diff, no commits yet). R1/R2 were independently rechecked. Round 2 is restricted to read-only verify entry semantics.
- Runtime recovery ruling: full exact original inventories and bytes must be restored and verified under a new versioned protocol. Preserve the old guard and its real lstat failure. New compatibility certification never changes historical contexts or claims historical physical identity. Design and implementation delegated to remaining9_source_review in a separate owned directory; independent review required before deployment.

- Task 2: fix round 2/5 (R3.1 addressed, zero open findings). Scoped reviewer spec PASS and quality PASS. Frozen driver 36649 B / d3e5e6ee3e5030e5e6f32ab3012560d2ff87aad8f8afa584e06210e50c5d61c7; review 07e24d86d10a7444ad43144fb02d65650973a2da729335f8345737b69194da2f. No cloud deployment or formal proof acceptance. Runtime recovery integration will be a separate reviewed task.
- Runtime diagnosis: job 6c10d8b2260942129995a021086c5f0b completed read-only in 43.064 s. All 34656 present files (8035660473 B) match the original snapshot; no extras or content differences. Missing exactly24923 files /7156488 B, all located and pin-checked on P1.

- Runtime installer: fix round 1/5 (I1/I2 addressed; zero open). Independent scoped spec and quality PASS, nine actual-filesystem tests passed without skips. Frozen installer3861a2ede46a42a8c7949f0624bd926c91d9c531808c934ae61b53ecb23a5023, review742d9d5e6ecd59645cefabcfd0991bca41fbee6fa2093e401ab0c5453f7294ff. No live restore or compatibility acceptance yet.

- Runtime byte checkpoint published on existing work branch by expected-head lease:447127edc4a97db1ebc3fa9c1793e390ef2e3e49, parent46d7a9b20373700d7e862116344abfb28243289f; commit includes [skip ci]. Only independently verified original-byte capsule and reviewed data installer; no new Lean source acceptance or runtime certificate claimed. Larger per-command transport parts were rejected INVALID_ARGUMENT without jobs; their plans remain preserved. Use immutable public Git bytes plus SHA checks in queued restore job6079f0f12f54499c9fe3f8f59ef52f9f.
- Task2b: consumer integration spec/quality PASS,19 local tests passed. Frozen driver50416aba871b79b6ddcc54af8264c8ee76cc018d08ad79726f52dc2d52fe6151; reviewerbef1258b70fc0ca9b1f37b2c1e2cd3028b836b0946837c6cc4b12c31bba1a59f. Producer review/capture remain separate gates.

- Live original-byte restore completed: job6079f0f12f54499c9fe3f8f59ef52f9f exit0 restored24923files/7156488B and independently reread exact bytes; original guard document preserved. RESTORED.json1630B/ea41d08947a6bd5463475ccb8f3589c3dcf6c3c02f921e15606ac9e569f1a496.
- Recovery capture v1 actually failed: jobdef7221c35934793ba6bb9736797a608 exit1, expected old physical-guard RuntimeError escaped a ValueError/FileNotFoundError handler. Original v1 code, bundle, task and stderr retained; no certificate, no old or new Lean. Producer fix round1/5 is limited to expected guard-error classification and a fresh v2 recovery root. Independent scoped review required before deployment.
- Consumer v2 root change independently spec/quality PASS: exactly1 byte changed in45345B driver; new SHAdc75e4c6d56df8673a6551420f74015b0b75d1fec3fe62b544ef63bcc596a133. Four binding paths updated; Shape stage still v1. Review2f2e90f3d8991ca7907908d9209dbfa09b1e9379500d0d102dbf0fbc3bc6fd96. Offline readback checker prepared; no capture or Shape acceptance yet.
- Producer runtime recovery round1/5 independently spec/quality PASS, no remaining scoped findings. Manifest1493B/e3f9588b43b5d3bb08a24f6938c1e6dde2e9968a719f06f28bbcd8166e822d3e; review7737B/26859e9ecde91897a85b372a6059e2a91d98e1536cc1c3497cc5e7484b36aa74. Exact local deployment bundle29252B/051a67f0196a5c7f2b62eaef1506331b4d53730120c8825e515db9a9ddb8bdb4 submitted to new recovery stagev2 as jobd1c729427f824000b03e75cf043325a5. Actual capture result pending; no Lean acceptance.
- Actual recovery capturev2 succeeded exit0 in117.597721s (jobd1c729427f824000b03e75cf043325a5):10roots/59579selected entries/8042816961B; original39+3+24accepted records preserved. Certificate4893B/3ce215e5339bf2363d6004c8427a3c8c5e8197d82ca6b933bf4e49d9aef1f089, export4245880B/8a0b3afab2c32114fc124a69071160f05a1c3dc8ef84d4a19b3ae4866a66b8c6. Full65-page reassembly matched external hash after tool2MiB log cap required2suffix jobs. Independent recovery-only readback PASS, report4777db55097e7b096a1951f27be6c41586e00e7d392458aa098376cfb8a86250. No old or new Lean commands.
- Shape exact five-file deployment and zero-proof preflight submitted as job935c122f42914d5d929ac6e7e4466d83. Binding967B/7425ce0a4d3c5907e55a74041f6f12456559f9d854a774fa648a16c2cd6f0f34. Three new strict checks remain pending actual preflight outcome.
- Task3 actual strict proof run64419527e8294cd2880cc7575368f6d5 succeeded exit0, exactly3 new modes,0old replays. normal3.864909589s/kernel3.641536297s/owned4.368042078s.40owned full types and declaration-module inventory,18printed axiom declarations,126project imports, same99952B object9907452a9498108f2212a5c5e881396ec6e1b84e4d2457e1e9f4dc0e540d40da. Strict read-only retained verifier f6f812506f494df7b3e601044ff38501 exit0; archive1057200B/3a7f08f9f47c68a25bbc300ea2124cbfecd5332a74e425e3dba494d0540630d4 fully recovered. Independent full readback PASS reportf4945da9830a798bc2734c1b2ea0e77cad2c0541e95b929b33b5840fa7e68115. Only Cell05 parse/decode/finite-shape; globalP2.6false. Work-branch publication pending.
