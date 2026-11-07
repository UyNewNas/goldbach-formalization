# P1 finite core extraction handoff

State: REQUESTED; worker WAITING_FOR_P0. SOURCE_ONLY, not compiled or kernel-validated.

## Frozen identity

- Baseline: `d41a7bc48b7066cd95c2a9e143a13e494d44b284`
- Worktree: `/workspace/shared/chen-coordination/p1-finite-core`
- 13-file source-tree digest: `b1948c9977884a9a12939fae4fb13e6616b8a26d40a6622978d5084a8c8598c1`
- Patch SHA256: `b8fd9e9b1d006191ac8351a0ce07c2aaa8a7f9a30d89796b6941cad6acf9219c`
- Manifest SHA256: `508a77771ded4cfa2b1a00a95d9cebfadbffa3aab55d3f30597418e34b542e56`

## What changed

- Moved 36 existing declarations from 10 mixed modules into FinitePrimeGeometryCore with byte-identical type/proof text and original fully qualified names.
- Every old module imports and re-exports the core; every retained declaration is unchanged. P1 and reindex change imports only.
- Actual fixed SmallRosser UpperAdmissibleSet/LowerAdmissibleSet objects remain upstream imports. No surrogate or relaxed hypothesis was introduced.
- Kept the original section-local noncomputability, open scopes, and namespace context; explicitly imported Mathlib.Order.Fin.Basic.
- Original goldbach, mathlib, LeanArchitect and toolchain pins are unchanged.

## Static evidence, with limits

- Ordinary Python checks: 36 declaration and doc blocks match exactly; 10 old modules remove only selected blocks and add one import; P1/reindex non-import bytes match exactly; authorized 13-path scope; git diff --check; patch reverse-apply check.
- Source import graph: 163 local + 506 goldbach + 9 Architect -> 27 local + 21 goldbach. No PNT, Wiener, ZetaBounds or PrimeReciprocalLogScale source path survives in the P1 closure; no cycles.
- Mathlib and other dependency imports are opaque pinned boundaries here. These are textual facts, not elaboration, kernel equivalence, or a proof-environment audit.
- P0 must force fresh compilation of the new core and the exact seven-gate P1 target, then perform the required replay and complete audits. Heavy compatibility-module and downstream regressions remain separate unpaid work.
- Do not combine stale heavy-module objects defining moved constants with the new core.

## Source hashes

- `ImbalancedChen/OrdinaryRosserFirstExitPolicy.lean`: `879ae0d1793467727abb01d9f9c753d8d8daa756f6462c9bd1cb22bcfa71b49b`
- `ImbalancedChen/FrozenRosserPolicy.lean`: `7dbad4ecc60d7ec5a7897c5836b5122a6f6eb0c88f66b4e4c014cecd06e1e165`
- `ImbalancedChen/PrimeHistoryLogCoordinates.lean`: `a141cd79142cc6775d271616dc914df14f162f7051ab02a77dac9c2b8db0ed37`
- `ImbalancedChen/FirstExitHistoricalLevels.lean`: `50b7c42ca4b987814a86fbd4b9264ad302f1f752126b857158f5115dd28b1e71`
- `ImbalancedChen/ActualPrimeBoxMass.lean`: `94c5186517af878ac3ffc38f19914ff848b40a2185ba9df1803efc444afb0e1a`
- `ImbalancedChen/ActualPrimeBoxTestFunctions.lean`: `2f2bee793b8d5054999bd0e71532f1f07ecf4ba69ba6cf98a0f840e4403e1203`
- `ImbalancedChen/OrdinaryUpperFiveAffineGates.lean`: `42084ece579d7cc0fe84648c8d81ac0c66b6ad237b019c36f305ed774728d3b3`
- `ImbalancedChen/OrdinaryPrimeFrontierAffineRegion.lean`: `5f5d781a5b177a84fbf52029b9a24262df711c50bcdf852cf0046cb76ef634e9`
- `ImbalancedChen/HistoricalPrefixCertificate.lean`: `b66bb9aae758648095779c507a20172e8ef9eee3f9647bf8c0b847c8a28ccfa9`
- `ImbalancedChen/HistoricalUpperFiveCellGeometry.lean`: `a5ca4e515e9bb1451dd1ebdf369cfaac34d7131e4877db0d0d351e06666ac410`
- `ImbalancedChen/FinitePrimeGeometryCore.lean`: `becd322d719aa8ae9f0cc7b3bedbc19b87edd347bbc79788ce8f6ca7e5694d85`
- `ImbalancedChen/FirstExitFrontierTupleReindex.lean`: `c42a94ac4802e8114667a4f3282e316746fd9b8beef9dce363440aee33f74452`
- `ImbalancedChen/HistoricalUnorderedThirdGeometry.lean`: `4ffa5f89e52a26f621f2e896d2fa4dd3c26508b887967eac696994ef4c54b129`

## Exact declaration migration

- `ImbalancedChen.ordinaryRosserPrefixAdmissible`: `ImbalancedChen/OrdinaryRosserFirstExitPolicy.lean:27` -> `ImbalancedChen/FinitePrimeGeometryCore.lean:31`; declaration SHA256 `36811e86bd27666a0ed2f18b48f33cbac022a5aa4aaa3cac2160f72bd2c4ac8f`
- `ImbalancedChen.ordinaryParityRosserPolicy`: `ImbalancedChen/OrdinaryRosserFirstExitPolicy.lean:293` -> `ImbalancedChen/FinitePrimeGeometryCore.lean:39`; declaration SHA256 `d2fb96e9216ae0742f685af34bae957662ea901c58333d5419ce9d6e62d5faa6`
- `ImbalancedChen.rosserAncestor`: `ImbalancedChen/FrozenRosserPolicy.lean:23` -> `ImbalancedChen/FinitePrimeGeometryCore.lean:52`; declaration SHA256 `d6b549be5290715d72d9cf30ff9f7bf01ea54f050e1da680e40aadcd95bb3044`
- `ImbalancedChen.ancestorFrozenPolicy`: `ImbalancedChen/FrozenRosserPolicy.lean:85` -> `ImbalancedChen/FinitePrimeGeometryCore.lean:57`; declaration SHA256 `2781d990a33467537ea0936c506d9105329ebe8d995e33ea307458118f8fa7b6`
- `ImbalancedChen.frozenParityRosserPolicy`: `ImbalancedChen/FrozenRosserPolicy.lean:93` -> `ImbalancedChen/FinitePrimeGeometryCore.lean:61`; declaration SHA256 `dfae07e4b455aef3fc9e7a3f0a35e72d46a6dd00e053f3ca02170e011a844556`
- `ImbalancedChen.primeHistoryTuple`: `ImbalancedChen/PrimeHistoryLogCoordinates.lean:27` -> `ImbalancedChen/FinitePrimeGeometryCore.lean:74`; declaration SHA256 `48fbcca51e0f20f2696dfe5dcc2cc357acaef1725876ee16677fc8690f512d09`
- `ImbalancedChen.primeHistoryLogCoordinates`: `ImbalancedChen/PrimeHistoryLogCoordinates.lean:32` -> `ImbalancedChen/FinitePrimeGeometryCore.lean:79`; declaration SHA256 `a3bfbb4779e280da4c22c5c5c016e4464a749205789506a94e9c00718698e14b`
- `ImbalancedChen.primeHistoryTuple_ofFn`: `ImbalancedChen/PrimeHistoryLogCoordinates.lean:37` -> `ImbalancedChen/FinitePrimeGeometryCore.lean:84`; declaration SHA256 `7b725be036419f3a907833c9f6f3d06ae3ae549aa1c81c8527f0647019c70aa0`
- `ImbalancedChen.primeHistoryTuple_reverse_ofFn`: `ImbalancedChen/PrimeHistoryLogCoordinates.lean:47` -> `ImbalancedChen/FinitePrimeGeometryCore.lean:94`; declaration SHA256 `6d8b88214a50299fb93be1c0b0fa86ca6483fff339437b845cef99dfab743545`
- `ImbalancedChen.primeHistoryTuple_reciprocal_mass`: `ImbalancedChen/PrimeHistoryLogCoordinates.lean:92` -> `ImbalancedChen/FinitePrimeGeometryCore.lean:100`; declaration SHA256 `228aa13b458d733cc4b0dea14eb6511e7f779f840f371170dbc0efd1af54e012`
- `ImbalancedChen.primeHistoryTuple_ancestor`: `ImbalancedChen/FirstExitHistoricalLevels.lean:65` -> `ImbalancedChen/FinitePrimeGeometryCore.lean:122`; declaration SHA256 `4694c6bb6f0bcca629cc6ecefc156df262c4e0670663717b0364d8f3d19ef358`
- `ImbalancedChen.primeHistoryLogCoordinates_ancestor`: `ImbalancedChen/FirstExitHistoricalLevels.lean:78` -> `ImbalancedChen/FinitePrimeGeometryCore.lean:135`; declaration SHA256 `2d4cbcbb56717cbf8b4090336905faf368b8ade3cd57f8b25bf1b3847fd26a88`
- `ImbalancedChen.thirdCappedUpperPolicy`: `ImbalancedChen/FirstExitHistoricalLevels.lean:86` -> `ImbalancedChen/FinitePrimeGeometryCore.lean:143`; declaration SHA256 `521795e1d4a529cb19d5a7b89e3bce5dad181f03b531a722ceb77d5abf9fb490`
- `ImbalancedChen.actualPrimeBoxTuples`: `ImbalancedChen/ActualPrimeBoxMass.lean:31` -> `ImbalancedChen/FinitePrimeGeometryCore.lean:157`; declaration SHA256 `2f6f1c50d508f021607797e002bd7b76ccdac48b66b6a99be58b2fb347006678`
- `ImbalancedChen.mem_actualPrimeBoxTuples_iff`: `ImbalancedChen/ActualPrimeBoxMass.lean:39` -> `ImbalancedChen/FinitePrimeGeometryCore.lean:165`; declaration SHA256 `d3028148d65b9558ad71b1e361f797ef7755d8ac3cff9fdae2e930c925de6f6f`
- `ImbalancedChen.actualPrimeTupleLog`: `ImbalancedChen/ActualPrimeBoxTestFunctions.lean:24` -> `ImbalancedChen/FinitePrimeGeometryCore.lean:183`; declaration SHA256 `26b9b35915ae3611c6de7712fe496a53331ced7b05cf6dc8cd151d63ff639c8d`
- `ImbalancedChen.actualPrimeTupleLog_rpow`: `ImbalancedChen/ActualPrimeBoxTestFunctions.lean:33` -> `ImbalancedChen/FinitePrimeGeometryCore.lean:186`; declaration SHA256 `46ca985ebb3777dbfd3e0a2508e82747582864d480a90811dddbf67db9bd20bd`
- `ImbalancedChen.mem_actualPrimeBoxTuples_log_iff`: `ImbalancedChen/ActualPrimeBoxTestFunctions.lean:42` -> `ImbalancedChen/FinitePrimeGeometryCore.lean:195`; declaration SHA256 `b34c52a38769709edf845be2f667fa1a6fa4f1c7593224897d65a0c0573eecc4`
- `ImbalancedChen.actualPrimeTupleLog_strictAnti_iff`: `ImbalancedChen/OrdinaryUpperFiveAffineGates.lean:51` -> `ImbalancedChen/FinitePrimeGeometryCore.lean:225`; declaration SHA256 `5f66d4fc98962aa4961497b360715671cd10012d251e21d269a8438e9942aa23`
- `ImbalancedChen.ordinaryUpperFive_cube_tests_iff_log`: `ImbalancedChen/OrdinaryPrimeFrontierAffineRegion.lean:92` -> `ImbalancedChen/FinitePrimeGeometryCore.lean:246`; declaration SHA256 `fcb5c5462990fe4d700f5a916a7b855190bf28133ea5032d065619dc713fa51d`
- `ImbalancedChen.historicalPrefixProject`: `ImbalancedChen/HistoricalPrefixCertificate.lean:27` -> `ImbalancedChen/FinitePrimeGeometryCore.lean:273`; declaration SHA256 `fc58d69da701ad171b1cd8e0963976a244727dd67e4325ffddef25e09da25cfd`
- `ImbalancedChen.mem_logPrimeMeshCell_historicalPrefixProject`: `ImbalancedChen/HistoricalPrefixCertificate.lean:39` -> `ImbalancedChen/FinitePrimeGeometryCore.lean:278`; declaration SHA256 `88adfb17b281cba5cacdc769ebaa455c28e8e49c5d5ddfe997433ef09ad075b7`
- `ImbalancedChen.primeHistoryLogCoordinates_eq_historicalPrefixProject`: `ImbalancedChen/HistoricalPrefixCertificate.lean:59` -> `ImbalancedChen/FinitePrimeGeometryCore.lean:288`; declaration SHA256 `01021fd28bf6773dbbf70513eecd348bb5d9c65e0749cdf2d0bb4bdcf60b0196`
- `ImbalancedChen.historicalPrefixLookup`: `ImbalancedChen/HistoricalPrefixCertificate.lean:67` -> `ImbalancedChen/FinitePrimeGeometryCore.lean:296`; declaration SHA256 `723466a4427d0756d8c219adef3de94d104e136a3bc5a9c8a4ca19b583acc93f`
- `ImbalancedChen.historicalPrefixLookup_on_cell`: `ImbalancedChen/HistoricalPrefixCertificate.lean:73` -> `ImbalancedChen/FinitePrimeGeometryCore.lean:302`; declaration SHA256 `f81f5f8cef8402f7dfaac9926dbb0802f4753ac9f2fa98231b1de4f642c6c9f4`
- `ImbalancedChen.historicalPrefixLookup_outside`: `ImbalancedChen/HistoricalPrefixCertificate.lean:88` -> `ImbalancedChen/FinitePrimeGeometryCore.lean:317`; declaration SHA256 `e8b30ee68a6652a12e7cd03e7bc4c441316ad915c51099a5ebd0691f086ccab3`
- `ImbalancedChen.historicalPrefixLookup_on_any_cell`: `ImbalancedChen/HistoricalPrefixCertificate.lean:98` -> `ImbalancedChen/FinitePrimeGeometryCore.lean:327`; declaration SHA256 `b8c506cc0ed7d11aa8da459c24faf07cefb6cefc4cc7b41adaee4424fedd78dd`
- `ImbalancedChen.HistoricalPrefixCapData`: `ImbalancedChen/HistoricalPrefixCertificate.lean:165` -> `ImbalancedChen/FinitePrimeGeometryCore.lean:346`; declaration SHA256 `9a4fcc2b0a8b714a2b4ed3796f4dcfe407bf3a70606a9affbce9ba95a89fd268`
- `ImbalancedChen.HistoricalPrefixCapData.cell3`: `ImbalancedChen/HistoricalPrefixCertificate.lean:179` -> `ImbalancedChen/FinitePrimeGeometryCore.lean:361`; declaration SHA256 `c23e100b2270d57726d7e6fcc6e851e41e1d7dfee8a26f3a67cc606109efc06a`
- `ImbalancedChen.HistoricalPrefixCapData.exponent3`: `ImbalancedChen/HistoricalPrefixCertificate.lean:256` -> `ImbalancedChen/FinitePrimeGeometryCore.lean:364`; declaration SHA256 `8d3f5578a4c3978528fe940cf32b6f5232c44300f6daae9ecd3c4f6fded7192d`
- `ImbalancedChen.HistoricalPrefixCapData.exponent3_on_cell`: `ImbalancedChen/HistoricalPrefixCertificate.lean:267` -> `ImbalancedChen/FinitePrimeGeometryCore.lean:367`; declaration SHA256 `40b7b10b99ab385a57c7d40c3b8b9f1a7b56bb7c266f2a781876ccd54fcabead`
- `ImbalancedChen.HistoricalPrefixCapData.level3`: `ImbalancedChen/HistoricalPrefixCertificate.lean:379` -> `ImbalancedChen/FinitePrimeGeometryCore.lean:374`; declaration SHA256 `67bdb9bd95646f90313ace366000095e623bfe39987f54e62d7c85932d8062b7`
- `ImbalancedChen.HistoricalPrefixCapData.upperThirdPolicy`: `ImbalancedChen/HistoricalPrefixCertificate.lean:437` -> `ImbalancedChen/FinitePrimeGeometryCore.lean:379`; declaration SHA256 `fc2aee1eed4fe3234686b5e6ad72f29e6275c49cd258a121fc45ba0aac478c26`
- `ImbalancedChen.HistoricalPrefixCapData.level3_on_fifth_cell`: `ImbalancedChen/HistoricalUpperFiveCellGeometry.lean:67` -> `ImbalancedChen/FinitePrimeGeometryCore.lean:398`; declaration SHA256 `45c6c58e32824404bf88f01ec8b632e9a8c3b5cccc639ab4c681a1cc06eddbfb`
- `ImbalancedChen.HistoricalPrefixCapData.level3_tuple_on_fifth_cell`: `ImbalancedChen/HistoricalUpperFiveCellGeometry.lean:114` -> `ImbalancedChen/FinitePrimeGeometryCore.lean:412`; declaration SHA256 `7018ebea4773cef79bfe287f205b2102af3370f6253014515bfafdf8e4ef7f83`
- `ImbalancedChen.historicalUpperFive_cube_tests_iff_log`: `ImbalancedChen/HistoricalUpperFiveCellGeometry.lean:195` -> `ImbalancedChen/FinitePrimeGeometryCore.lean:435`; declaration SHA256 `55cdf9fb8ff4d0690f697bca9b471c3cf00dcd50f1ab0899396c29fc8be07dd6`

Full original blocks, types and proof bodies are in declaration-migration.json. REQUESTED.json carries the exact validation request and prior mathematical obligations.

No Lean, Lake, leanchecker, proof-environment audit, CI, installation, commit, push or publication was run.
