# Task 1 source extraction report

## Staged change

The three new owners contain exactly two, six and five original declaration blocks. `Part3MediumAtomCore` keeps all thirteen `MediumAtom` fields in the original order. `Part3ActualNonzeroSourceCore` keeps the same signed residue, divisible-factor quotient image, real frequency ceiling, signed integer window, and literal nonzero filter. `Part3PrimaryDyadicActualMode` keeps both sign choices and both coefficient parameters as written.

The manuscript reference is commit `8ca3f6a7f6bbaf6f67c96e80a5065eca9838e703`, `paper/release-20261106/en/analytic-appendix.tex`. The frozen local copy places the beta definition at line 601, the independent finite coefficient and coprimality conditions at 609–620, and the signed support and energy language at 673–687. This change relocates existing Lean declarations for that finite specialization.

## Provenance checks

- The frozen intake SHA-256 values matched all thirteen declarations. Independent extracts from `b945f39a1e355ff4fcca9865ab59ffc97f2172c0` matched all thirteen blocks and selected docs. The eight provider blocks additionally matched `34201be0ca95d465336119fce24b7681c17ab0c6`; the five wrapper declarations also matched registered donor blobs `7b3374576687df50307ef847aa51e9fef15dddae` and `3a12da5b72eeddd3558c4714eecd7754cd660a55`.
- The `actual_nonzero_coprime` extraction ends on `dyadicBeta_coprime hb`. The closing section command lies outside the hashed block. Leading docs are separately checked byte for byte.
- The six providers retain exact source bytes after declared removal of selected lines and addition of one import. The check removed each added import and reinserted the original byte ranges, reconstructing the entire frozen donor. Both import-only wrappers retain the exact original import bytes and add `Part3PrimaryDyadicActualMode`.
- The combined auditor uses the eleven-module auditor unchanged apart from the added import and module list entries. The unchanged shared Python verifier receives all fourteen modules in dependency order and binds the entry point plus the common and actual move ledgers.
- A separate Python check reproduced every source and target declaration/doc range, rechecked every staged file and frozen donor digest, reconstructed the donor remainders, verified the import order, and scanned source using the shared forbidden-proof lexer. It ran without Lean.

## Frozen draft file identities

Frozen working-tree input was read at Git HEAD `dc2aeb2e2f7e154d84ca7e258fa9461eef373923` with the common source patch already staged. The installation base is `45b73d26b35cb83bb9dae22079282a0a143837a3`. The hashes below identify the first frozen draft. The final ledger hash appears in the compiler evidence section.

| Path | Original SHA-256 | Staged SHA-256 |
| --- | --- | --- |
| `ImbalancedChen/Part3ActualM2FinitePoissonAdapter.lean` | `a608ffd41a6425eea9b03ab99cac5bd6971417082ac20c115a3baac887ed5b5f` | `cc7c99ae198bb7356c776a63a377b7a4bdddb0ae6fbd158d250691bdf2130946` |
| `ImbalancedChen/Part3ActualModeJointBetaPositiveCount.lean` | `f56bd1ee5294fb62a1f5c0fc003908f61daa190a2cf4c4ade84e7a0e9f74504e` | `10ca24626d4661639fac6c7764b450ef7d69d152b6b6955e773c0fb2e044491b` |
| `ImbalancedChen/Part3ActualNonzeroSourceCore.lean` | new file | `6d2d4c3e192f795c1bc2ec1c5bd3d16a4f161c5cf8d4c4446e85fdd26bb4080b` |
| `ImbalancedChen/Part3ActualPositiveLatticeSmoothCover.lean` | `6e4dbe90aa13cdd346bb93589733d6469a96d60cdf50c6df33a5c46971821da9` | `b7a59219105dbffbb98144e633a4ecc0c857baf4f6000f25c598fc32c5c31612` |
| `ImbalancedChen/Part3ActualSeparatedRowFiniteMatcher.lean` | `c668788542424f65003dec6586af9aee814b4e9f4fd7246714eec7815b1f1fe0` | `c662f859073df69308adc7a26f40d7e4eb99638eeb63ccf5ba643fe97b21e408` |
| `ImbalancedChen/Part3DistributionTargets.lean` | `96eab9f8fd29a0fc7660bc7ec973d7a73f2aebb35e2644ac040de4b5eb659330` | `4b56000c87df6abfb4dc3c5ff32e22f83c8aa2bd44cec10403b07cc4c66d8e98` |
| `ImbalancedChen/Part3MediumAtomCore.lean` | new file | `e62c03731340b62a68ea9636864a891c428395f7af75345d682ea195707526e5` |
| `ImbalancedChen/Part3PrimaryDyadicActualMode.lean` | new file | `32b3974bbab217a7bfa50ebc6331dd9bb9432fb64fcb28e8423503812a39e9b6` |
| `ImbalancedChen/Part3SharedFirstFactorSmallCoreSmoothFrequency.lean` | `2c542a1aad86b505798e83cc1564ee751b763921c6f9dda6289750307328f9fd` | `d645486f9c3d25090c117e9ad02d1e7261c0c1b7c6da793267a2e56cedb0729f` |
| `ImbalancedChen/Part3ZActualPrimaryDyadicAssembly.lean` | `ab1e01267b527dad8781786f29af3b21380ba5a1c635755306ded1af281ab589` | `d6da2a6705bd8892aad97ef3d44f86e31de85caf26e38b0c09e0b9287f7ee07c` |
| `ImbalancedChen/Part3ZActualPrimaryShortEndpoint.lean` | `980e83304e25c226119b39e37da6b0f3c5c9ccdaa3e2ded402b61da911ca87c4` | `20d2298fa39b544b611bcbf8d5c25c70db659fb8e31d540f4848801fb0665812` |
| `docs/part3-distribution/p34-common-phase-20261126/ACTUAL_DECLARATION_MOVES.json` | new file | `b321531ff1cc11a68729a24ded189d8f4c2b387168164ad1a1efd2cda3235bc5` |
| `verification/P34PrimaryActualModeAudit.lean` | new file | `058da092432f7b0836fde4b80696b7ae7cd244d843e7ec2a3795c5bc359fb2cc` |
| `verification/verify_p34_primary_actual_mode.py` | new file | `1e7bf6a415492f64a8e376ac51385367ffaadb62fb77f0efb278f0694821a80e` |

## Focused compiler input

- `ImbalancedChen/Part3MediumAtomCore.lean`
- `ImbalancedChen/Part3ActualNonzeroSourceCore.lean`
- `ImbalancedChen/Part3PrimaryDyadicActualMode.lean`
- `verification/P34PrimaryActualModeAudit.lean`

## Focused compiler evidence

P3 job `836562cf0f174ae0af3b8e75babf915a` strictly compiled and replayed all three new owners and ran the full fourteen-module inventory. Every recorded stage exited 0. The complete defining-module inventory matched the serialized constant lists and contained 235 declarations. The prior 192 owner/type/axiom records matched the focused common receipt exactly. The three new owners contained these records.

| Owner | Total records | Moved declarations | Other generated or private declarations |
| --- | ---: | ---: | ---: |
| `Part3MediumAtomCore` | 30 | 2 | 28 |
| `Part3ActualNonzeroSourceCore` | 8 | 6 | 2 |
| `Part3PrimaryDyadicActualMode` | 5 | 5 | 0 |

The two additional actual-source records are `ImbalancedChen.Part3.ActualSeparatedRowPacketMatchSourceOnly.signedResidue.eq_1` and `ImbalancedChen.Part3.MediumAtom.sharedSmoothFrequencyBound._proof_1`. The combined inventory excludes `ImbalancedChen.Part3.CommonCompletedVariable.weight.eq_1`. The shared audit accepted only `Classical.choice`, `Quot.sound`, and `propext` as transitive axioms. The ledger binds compiler source and object hashes and every new owner record, including the generated names, elaborated-type digests and transitive axioms. The source required zero proof repairs.

| Evidence | SHA-256 |
| --- | --- |
| Focused report | `83f5e7de13cb97b05d98a754bc729f1697efa74d4e8375a9a5f9182992dcde16` |
| Full joint declarations JSON | `6999a1e6de1d2545e2b109e5771e5847074a6b8dd45f1d157a2eaa88d342b4b0` |
| Full joint audit log | `1cd9a86b7dc7994b637a30dcc3ec3347e851b803111f80b2a5e9236fc8ea7006` |
| Focused evidence ZIP | `bba37abb1a20902128e9d34509556fe3f7ae9822d27a42d7eebba26743c4a79b` |
| Committed actual move ledger | `a5abd2a87d0ee6348d5897d94d5c46c6370c623b8949a7ce40f3337bbc77cf24` |

## Exact source handoff

- Source commit `b8e4b3c724e8ec5b6fd6e4db403e0139d57bf306`
- Source tree `39555f9fd51a8dc10ad07797b20d60621a222854`
- Parent `45b73d26b35cb83bb9dae22079282a0a143837a3`

All 14 committed path digests match the final guarded manifest. The worktree was clean and the shared verifier passed the exact-HEAD source-only check. The two existing source-provenance tests passed. The focused proof receipt establishes the three newly compiled owners with eleven reused compatible objects. Root owns the pending exact-tree publication and fourteen-module zero-project-object gate. These checks cover the finite specialization and leave the original-row and spectral interfaces outside this task.
