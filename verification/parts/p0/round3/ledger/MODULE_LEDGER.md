# Part 0 第三批组件台账候选

生成：2026-10-12T12:28:34.540729+00:00。本文件由 `build_ledger.py` 从固定源码和已有原始回执编目；本次没有执行 Lean、Lake、内核重放或 CI。

**31 个固定生产模块中，19 个达到组件接收条件，12 个仍未全接收。新增 8 个组件有 198 个所属声明，累计 591 个。台账写入时新集成 SHA 尚未生成，整根构建、根重放、根公理检查及新增完整类型输出均为 pending；后续以该实际 SHA 的 Actions artifact 更新机器结果。**

机器台账见 [module-ledger.json](module-ledger.json)，全部 591 条接受组件声明的编译器记录见 [compiler-declarations.json](compiler-declarations.json)。该清单逐项标明 `PP_ALL` 或 `DEFAULT_PRETTY`；不能把两者混称完整显式输出。

## 固定版本与口径

| 对象 | 完整 SHA / 状态 |
| --- | --- |
| 共同证明基线 | `1a80c1bcce67886f699d097fc37fd245cd3620bf` |
| 手稿基线 | `ba6ec11d800eccc54406490631895e174de85766` |
| 首轮 P0 文档 | `9fe1d6b8b68a97cad3a122410ad7fde1701eed35` |
| 上轮 P0 交付 | `80aca6710c83b5160f4c5fdd05d180e507990e95` |
| 当前实有 P0 固定来源 | `cce2334906f068fda2f58c400646366f2aa2d417` |
| 新集成 SHA | **pending；本候选不自行生成集成提交** |
| P1 证明 / 后续文档 | `b09d5361e0b30f3e85cb912a03c7bfb85a99bf8f` / `7f894bfb57b7aa561360e335c6d610b7c30614e0` |
| P2 证明 / 交接 | `6acf61cc28f227a9154363f2347c386ec01dffb0` / `076473720210ee602e6e9735902e16bb6c5f1398` |
| P3 固定交接 | `f37f341412eb239f7e7e8937921ee8d01c9c2922` |
| P4 生产 / 最新交接 | `262f69822a386a9d44efc059bceba11049668d68` / `3d5dd058cf6bef5fe90719ee277580baf8b5bf41` |
| P5 最新固定交接 | `bf54caeb5e708474cacefac13a171d307b4c64f2` |

这里的“组件接收”表示固定源和既有编译、原装重放、公理审计回执已对应；新增 8 个叶模块仍需由 P0 写入公共根并绑定新集成 SHA。旧 11 个组件已在此前 P0 生产树。

## 已执行验证的边界

CCE 的原始 artifact 绑定 `cce2334906f068fda2f58c400646366f2aa2d417`：完整 `lake build` 成功 **9790 jobs / 3226 秒**，根 `leanchecker` 成功 **506 秒**，根公理检查成功 **5260 个 ImbalancedChen 声明 / 31 秒**。
回执：[provenance](../prior-ci/cce-core/provenance.log)、[outcomes](../prior-ci/cce-core/outcomes.log)、[build](../prior-ci/cce-core/build.log)、[replay](../prior-ci/cce-core/leanchecker.log)、[axioms](../prior-ci/cce-core/axiom-audit.log)。

已读取本地固定 Git diff：CCE 相对 80aca 仅改 `.github/workflows/lean.yml`，job timeout 为 150 分钟、build timeout 为 90 分钟，生产源码不变。**这些通过只属于 CCE 旧根；不能套到新增根或未被旧根导入的模块。**

新增组件复用已有同版本成功记录：P1 四模块 strict/replay/所属声明审计；P3 Normalization 三门及 4957 模块导入身份；P2 Geometry/Prefix4Data/Prefix4 三门、完整声明审计以及已完成的专用 CI。没有重启同版本健康任务。

## 声明数与完整类型

| 来源 | 所属声明审计 | 完整显式 pp.all | 默认 pretty 无 `⋯`/`…` | 默认 pretty 有省略 |
| --- | ---: | ---: | ---: | ---: |
| 上轮已接收 11 模块 | 393 | 393 | 0 | 0 |
| 本轮 P1 四模块 | 140 | **0** | 133 | 7 |
| 本轮 P3 Normalization | 2 | 2 | 0 | 0 |
| 本轮 P2 三模块 | 56 | 56 | 0 | 0 |
| 接受组件合计 | **591** | **451** | **133** | **7** |

P1 的 7 项省略均在 HistoricalPrefixCertificate；133 项没有省略标记仍不等于 pp.all。P1 的 probe 另有 10 声明，未混入生产 140。P0 正在准备新固定 SHA 下的 198 新声明和主条件桥完整类型输出，本候选只记录 pending。

## 模块清单

表中三门依次为严格编译 / 原装生产重放 / 全所属声明公理审计；“未达”指依赖超时，目标没有完成，“legacy+”指 producer 确实返回 0 但 P0 要求的导入对象绑定仍缺失。每项源码哈希与固定 SHA 在后面的明细中完整打印。

| 模块 | 归属 | 三门 | 所属声明 | 接收 |
| --- | --- | --- | ---: | --- |
| `ActualSelectedPrefixLowerCellSum` | P1 | 通过 / 通过 / 通过 | 9 | 组件接收 |
| `ActualSelectedPrefixLowerOwnCubeIntegral` | P1 | 通过 / 通过 / 通过 | 8 | 组件接收 |
| `HistoricalPrefixCertificate` | P1 | 通过 / 通过 / 通过 | 96 | 组件接收 |
| `OrdinaryLowerFourFrontier` | P1 | 通过 / 通过 / 通过 | 27 | 组件接收 |
| `Certificates.AboveMuSecondCoarse` | P2 | 通过 / 通过 / 通过 | 71 | 组件接收 |
| `Certificates.PairedCertificateChecker` | P2 | 通过 / 通过 / 通过 | 58 | 组件接收 |
| `Certificates.PairedFibreIntegral` | P2 | 通过 / 通过 / 通过 | 13 | 组件接收 |
| `Certificates.PairedV2` | P2 | 通过 / 通过 / 通过 | 46 | 组件接收 |
| `Certificates.PairedV2Data` | P2 | 通过 / 通过 / 通过 | 18 | 组件接收 |
| `Certificates.RationalLogCertificate` | P2 | 通过 / 通过 / 通过 | 47 | 组件接收 |
| `Part3CurrentLowerDistribution` | P3 | 待验证 / 待验证 / 待验证 | — | 候选 |
| `Part3DistributionTargets` | P3 | 待验证 / 待验证 / 待验证 | — | 候选 |
| `Part3LongSlotDistribution` | P3 | 通过 / 通过 / 通过 | 35 | 组件接收 |
| `Part3LongSlotNormalization` | P3 | 通过 / 通过 / 通过 | 2 | 组件接收 |
| `Part3PrimeAPDistribution` | P3 | 待验证 / 待验证 / 待验证 | — | 候选 |
| `Part3RoughAuxiliarySW` | P3 | 待验证 / 待验证 / 待验证 | — | 候选 |
| `Part3RoughAuxiliarySWNormalization` | P3 | 待验证 / 待验证 / 待验证 | — | 候选 |
| `ActualUpperDensityAssembly` | P4-A | 未达 / 未达 / 未达 | — | 候选 |
| `ActualUpperPolicyDensity` | P4-A | 未达 / 未达 / 未达 | — | 候选 |
| `RealPhysicalUpperWeightBridge` | P4-B | 未达 / 未达 / 未达 | — | 候选 |
| `RealUpperCountingAssembly` | P4-B | 未达 / 未达 / 未达 | — | 候选 |
| `UpperCoefficientPerturbation` | P4-A | 未达 / 未达 / 未达 | — | 候选 |
| `CurrentChenBuchstabRefinement` | P5 | 通过 / 通过 / 通过 | 5 | 组件接收 |
| `CurrentChenLowerScale` | P5 | 通过 / 通过 / 通过 | 5 | 组件接收 |
| `CurrentChenMeanLedger` | P5 | 通过 / 通过 / 通过 | 93 | 组件接收 |
| `CurrentPairedBuchstabBridge` | P0 | 通过 / 通过 / 通过 | 2 | 组件接收 |
| `CurrentChenInitialSource` | P5 | legacy+ / legacy+ / legacy+ | 8 | 候选 |
| `CurrentChenInitialMean` | P5 | 待验证 / 待验证 / 待验证 | — | 候选 |
| `Certificates.PairedV2Geometry` | P2 | 通过 / 通过 / 通过 | 10 | 组件接收 |
| `Certificates.PairedV2Prefix4Data` | P2 | 通过 / 通过 / 通过 | 11 | 组件接收 |
| `Certificates.PairedV2Prefix4` | P2 | 通过 / 通过 / 通过 | 35 | 组件接收 |

## 逐模块固定身份、回执与未闭合输入

### ImbalancedChen.ActualSelectedPrefixLowerCellSum

- 文件：[ImbalancedChen/ActualSelectedPrefixLowerCellSum.lean](snapshot-sources/ImbalancedChen/ActualSelectedPrefixLowerCellSum.lean)；归属 **P1**；接收方：P1, P2, P5。
- 当前证明源固定 SHA：`b09d5361e0b30f3e85cb912a03c7bfb85a99bf8f`；最新固定交接：`7f894bfb57b7aa561360e335c6d610b7c30614e0`。
- 源码 SHA256：`48b9b1b50d1fec780378e61a5250971cf0f5222b12fcf04706ad357f90040714`；Git blob：`64e73f036cd309512ea5513377cb0528e65ed524`。
- 对象 SHA256：`2c39f6f4768a0e60fb7d93bc7f487c7a31ebcfb188b4e82705d3dbecf25e1648`。
- 组件状态：`RECEIPT_ACCEPTED_PENDING_NEW_INTEGRATION_SHA`；新增根固定 SHA：pending。
- 编译：`PASS_STRICT_TRUST0`，exit=0，214.859 秒；[回执](../intake/p1-intake/P1_RECEIPT_REUSE.json)。
- 生产重放：`PASS_ORIGINAL_LEANCHECKER`，exit=0，28.921 秒；[回执](../intake/p1-intake/P1_RECEIPT_REUSE.json)。
- 公理审计：`PASS_EXACT_OBJECT_ALL_OWNED_DECLARATIONS`，exit=0，427.006 秒；[回执](../intake/p1-intake/P1_RECEIPT_REUSE.json)。
- 声明：所属审计 9；pp.all 0；默认 pretty 9（有省略 0）。
- 未闭合输入：采用的 cell/cap/mask 字典、真实积分数值证书与 row 绑定尚待供应。；每 cell 的整盒许可、完整覆盖和不重计尚待与实际采用表接合。；同一 boxed physical rho 的身份、支持、因式分解、分布及 compiler 误差尚未闭合。；完整历史第五/第六/第八积分、截断误差和全局 K 尚待提供。；完整十一项采用均值、真实 c、hLower、hUpper 尚无实际供应者。。

### ImbalancedChen.ActualSelectedPrefixLowerOwnCubeIntegral

- 文件：[ImbalancedChen/ActualSelectedPrefixLowerOwnCubeIntegral.lean](snapshot-sources/ImbalancedChen/ActualSelectedPrefixLowerOwnCubeIntegral.lean)；归属 **P1**；接收方：P1, P2, P5。
- 当前证明源固定 SHA：`b09d5361e0b30f3e85cb912a03c7bfb85a99bf8f`；最新固定交接：`7f894bfb57b7aa561360e335c6d610b7c30614e0`。
- 源码 SHA256：`c98fd3407d59f27cd140689de36f888cfd804130dc9787e3e60ea451b4e1dcd1`；Git blob：`6a535380f1bb4074e06ff8ce4180eaae63d2e9fe`。
- 对象 SHA256：`882bd542ca63d00c6776ad65d855070832358bcacbc14206b90f68c3900cf90e`。
- 组件状态：`RECEIPT_ACCEPTED_PENDING_NEW_INTEGRATION_SHA`；新增根固定 SHA：pending。
- 编译：`PASS_STRICT_TRUST0`，exit=0，94.948 秒；[回执](../intake/p1-intake/P1_RECEIPT_REUSE.json)。
- 生产重放：`PASS_ORIGINAL_LEANCHECKER`，exit=0，48.552 秒；[回执](../intake/p1-intake/P1_RECEIPT_REUSE.json)。
- 公理审计：`PASS_EXACT_OBJECT_ALL_OWNED_DECLARATIONS`，exit=0，427.006 秒；[回执](../intake/p1-intake/P1_RECEIPT_REUSE.json)。
- 声明：所属审计 8；pp.all 0；默认 pretty 8（有省略 0）。
- 未闭合输入：采用的 cell/cap/mask 字典、真实积分数值证书与 row 绑定尚待供应。；每 cell 的整盒许可、完整覆盖和不重计尚待与实际采用表接合。；同一 boxed physical rho 的身份、支持、因式分解、分布及 compiler 误差尚未闭合。；完整历史第五/第六/第八积分、截断误差和全局 K 尚待提供。；完整十一项采用均值、真实 c、hLower、hUpper 尚无实际供应者。。

### ImbalancedChen.HistoricalPrefixCertificate

- 文件：[ImbalancedChen/HistoricalPrefixCertificate.lean](snapshot-sources/ImbalancedChen/HistoricalPrefixCertificate.lean)；归属 **P1**；接收方：P1, P2, P4-A, P5。
- 当前证明源固定 SHA：`b09d5361e0b30f3e85cb912a03c7bfb85a99bf8f`；最新固定交接：`7f894bfb57b7aa561360e335c6d610b7c30614e0`。
- 源码 SHA256：`b6ef2c6febc61e28ddf5bbeb5c02fd665e5266833df4cd1b5b2640481cb6e6f3`；Git blob：`9c5d05230b05f102f10cb8dd086942dfc665fa3f`。
- 对象 SHA256：`d0a2da752c3ea606971f34aabe8e7beaad8ca1a34788cfe44634955efbd5d005`。
- 组件状态：`RECEIPT_ACCEPTED_PENDING_NEW_INTEGRATION_SHA`；新增根固定 SHA：pending。
- 编译：`PASS_STRICT_TRUST0`，exit=0，93.78 秒；[回执](../intake/p1-intake/P1_RECEIPT_REUSE.json)。
- 生产重放：`PASS_ORIGINAL_LEANCHECKER`，exit=0，47.087 秒；[回执](../intake/p1-intake/P1_RECEIPT_REUSE.json)。
- 公理审计：`PASS_EXACT_OBJECT_ALL_OWNED_DECLARATIONS`，exit=0，427.006 秒；[回执](../intake/p1-intake/P1_RECEIPT_REUSE.json)。
- 声明：所属审计 96；pp.all 0；默认 pretty 96（有省略 7）。
- 未闭合输入：采用的 cell/cap/mask 字典、真实积分数值证书与 row 绑定尚待供应。；每 cell 的整盒许可、完整覆盖和不重计尚待与实际采用表接合。；同一 boxed physical rho 的身份、支持、因式分解、分布及 compiler 误差尚未闭合。；完整历史第五/第六/第八积分、截断误差和全局 K 尚待提供。；完整十一项采用均值、真实 c、hLower、hUpper 尚无实际供应者。。

### ImbalancedChen.OrdinaryLowerFourFrontier

- 文件：[ImbalancedChen/OrdinaryLowerFourFrontier.lean](snapshot-sources/ImbalancedChen/OrdinaryLowerFourFrontier.lean)；归属 **P1**；接收方：P1, P2, P5。
- 当前证明源固定 SHA：`b09d5361e0b30f3e85cb912a03c7bfb85a99bf8f`；最新固定交接：`7f894bfb57b7aa561360e335c6d610b7c30614e0`。
- 源码 SHA256：`97f5e3390d9c90a9598a7fa5fa1ede84c174da9497f23c88be6ea04ffb0bc9e8`；Git blob：`05f0e3758e0b6fa0cfa6b3002e9c61ce164489ae`。
- 对象 SHA256：`9ddc1d019438b9d9b8f3ed31ea643c160f3f5cd8128c227f91eca5697c542026`。
- 组件状态：`RECEIPT_ACCEPTED_PENDING_NEW_INTEGRATION_SHA`；新增根固定 SHA：pending。
- 编译：`PASS_STRICT_TRUST0`，exit=0，200.131 秒；[回执](../intake/p1-intake/P1_RECEIPT_REUSE.json)。
- 生产重放：`PASS_ORIGINAL_LEANCHECKER`，exit=0，68.232 秒；[回执](../intake/p1-intake/P1_RECEIPT_REUSE.json)。
- 公理审计：`PASS_EXACT_OBJECT_ALL_OWNED_DECLARATIONS`，exit=0，427.006 秒；[回执](../intake/p1-intake/P1_RECEIPT_REUSE.json)。
- 声明：所属审计 27；pp.all 0；默认 pretty 27（有省略 0）。
- 未闭合输入：采用的 cell/cap/mask 字典、真实积分数值证书与 row 绑定尚待供应。；每 cell 的整盒许可、完整覆盖和不重计尚待与实际采用表接合。；同一 boxed physical rho 的身份、支持、因式分解、分布及 compiler 误差尚未闭合。；完整历史第五/第六/第八积分、截断误差和全局 K 尚待提供。；完整十一项采用均值、真实 c、hLower、hUpper 尚无实际供应者。。

### ImbalancedChen.Certificates.AboveMuSecondCoarse

- 文件：[ImbalancedChen/Certificates/AboveMuSecondCoarse.lean](snapshot-sources/ImbalancedChen/Certificates/AboveMuSecondCoarse.lean)；归属 **P2**；接收方：P1, P2, P4-A。
- 当前证明源固定 SHA：`5e31713690daba5ff926da61875a99171718fd1d`；最新固定交接：`076473720210ee602e6e9735902e16bb6c5f1398`。
- 源码 SHA256：`85fdde51712d86400c19e3175b8f5f4aebe7efeadd7c2b9357fea0bc5a8759c2`；Git blob：`c2d0b52b285cbc584b64e07eebd7f8593459491d`。
- 对象 SHA256：`bad1e9e5ffd1b3fe62e7578a52749bdae13050dbfe892d5beee6b61efe24e470`。
- 组件状态：`PREVIOUSLY_ACCEPTED_EXACT_SOURCE`；新增根固定 SHA：pending。
- 编译：`PASS_STRICT_TRUST0`；[回执](history/round2/ledger-delivery/module-ledger.json)。
- 生产重放：`PASS_ORIGINAL_LEANCHECKER`；[回执](history/round2/ledger-delivery/module-ledger.json)。
- 公理审计：`PASS_OWNED_DECLARATIONS`；[回执](history/round2/ledger-delivery/module-ledger.json)。
- 声明：所属审计 71；pp.all 71；默认 pretty 0（有省略 0）。
- 未闭合输入：E1 geometry and saved-floor meaning；remaining adopted rows；full historical arithmetic parent licence；global union integral/coverage and no double count；all lower and upper integral ledger terms；two actual reserves；same actual rho density；full c, hLower and hUpper。

### ImbalancedChen.Certificates.PairedCertificateChecker

- 文件：[ImbalancedChen/Certificates/PairedCertificateChecker.lean](snapshot-sources/ImbalancedChen/Certificates/PairedCertificateChecker.lean)；归属 **P2**；接收方：P2, P0。
- 当前证明源固定 SHA：`c9f407efe66240c08c2e8a678330ba7b98b74db5`；最新固定交接：`076473720210ee602e6e9735902e16bb6c5f1398`。
- 源码 SHA256：`454c02ef9db5ea4f50deec917ff00809e5c27f0a480b2bf8f150f01e201d227c`；Git blob：`825ee28f923e5ef5144a3cf0f7eb263d45016319`。
- 对象 SHA256：`46d84fd7f1625e3f55b20048ea52ae5835720b22f0b50ceee255b8175563f78c`。
- 组件状态：`PREVIOUSLY_ACCEPTED_EXACT_SOURCE`；新增根固定 SHA：pending。
- 编译：`PASS_STRICT_TRUST0`；[回执](history/round2/ledger-delivery/module-ledger.json)。
- 生产重放：`PASS_ORIGINAL_LEANCHECKER`；[回执](history/round2/ledger-delivery/module-ledger.json)。
- 公理审计：`PASS_OWNED_DECLARATIONS`；[回执](history/round2/ledger-delivery/module-ledger.json)。
- 声明：所属审计 58；pp.all 58；默认 pretty 0（有省略 0）。
- 未闭合输入：E1 geometry and saved-floor meaning；remaining adopted rows；full historical arithmetic parent licence；global union integral/coverage and no double count；all lower and upper integral ledger terms；two actual reserves；same actual rho density；full c, hLower and hUpper。

### ImbalancedChen.Certificates.PairedFibreIntegral

- 文件：[ImbalancedChen/Certificates/PairedFibreIntegral.lean](snapshot-sources/ImbalancedChen/Certificates/PairedFibreIntegral.lean)；归属 **P2**；接收方：P2, P5。
- 当前证明源固定 SHA：`c9f407efe66240c08c2e8a678330ba7b98b74db5`；最新固定交接：`076473720210ee602e6e9735902e16bb6c5f1398`。
- 源码 SHA256：`d8bcdab8e5010d16827f5074db713243adc6a1cd686ab2b69bd3f9b4e41039a4`；Git blob：`9c9243c22c6359a93169f43f1e2155b6e1a19ecd`。
- 对象 SHA256：`d974979205e82a178755d8b2bdde4c3aca7da742dde60a563bb80ef6314aa3ba`。
- 组件状态：`PREVIOUSLY_ACCEPTED_EXACT_SOURCE`；新增根固定 SHA：pending。
- 编译：`PASS_STRICT_TRUST0`；[回执](history/round2/ledger-delivery/module-ledger.json)。
- 生产重放：`PASS_ORIGINAL_LEANCHECKER`；[回执](history/round2/ledger-delivery/module-ledger.json)。
- 公理审计：`PASS_OWNED_DECLARATIONS`；[回执](history/round2/ledger-delivery/module-ledger.json)。
- 声明：所属审计 13；pp.all 13；默认 pretty 0（有省略 0）。
- 未闭合输入：E1 geometry and saved-floor meaning；remaining adopted rows；full historical arithmetic parent licence；global union integral/coverage and no double count；all lower and upper integral ledger terms；two actual reserves；same actual rho density；full c, hLower and hUpper。

### ImbalancedChen.Certificates.PairedV2

- 文件：[ImbalancedChen/Certificates/PairedV2.lean](snapshot-sources/ImbalancedChen/Certificates/PairedV2.lean)；归属 **P2**；接收方：P2, P5, P4-A。
- 当前证明源固定 SHA：`c9f407efe66240c08c2e8a678330ba7b98b74db5`；最新固定交接：`076473720210ee602e6e9735902e16bb6c5f1398`。
- 源码 SHA256：`e8b6cdf4c1bbf9382c58b9002704183b3608f15e57f2d0837b5157f93d41eef7`；Git blob：`69ed77e5bb63b34c447d5da409660ad196b74559`。
- 对象 SHA256：`b5ef6a818d102157193e07b7c874f46d6cbeaa7cce5b4b00397ff6b2d4fe3491`。
- 组件状态：`PREVIOUSLY_ACCEPTED_EXACT_SOURCE`；新增根固定 SHA：pending。
- 编译：`PASS_STRICT_TRUST0`；[回执](history/round2/ledger-delivery/module-ledger.json)。
- 生产重放：`PASS_ORIGINAL_LEANCHECKER`；[回执](history/round2/ledger-delivery/module-ledger.json)。
- 公理审计：`PASS_OWNED_DECLARATIONS`；[回执](history/round2/ledger-delivery/module-ledger.json)。
- 声明：所属审计 46；pp.all 46；默认 pretty 0（有省略 0）。
- 未闭合输入：E1 geometry and saved-floor meaning；remaining adopted rows；full historical arithmetic parent licence；global union integral/coverage and no double count；all lower and upper integral ledger terms；two actual reserves；same actual rho density；full c, hLower and hUpper。

### ImbalancedChen.Certificates.PairedV2Data

- 文件：[ImbalancedChen/Certificates/PairedV2Data.lean](snapshot-sources/ImbalancedChen/Certificates/PairedV2Data.lean)；归属 **P2**；接收方：P2, P0。
- 当前证明源固定 SHA：`c9f407efe66240c08c2e8a678330ba7b98b74db5`；最新固定交接：`076473720210ee602e6e9735902e16bb6c5f1398`。
- 源码 SHA256：`a9fa2f53e2adca9b61efdf0ed6992d22b79b7807d10f0921154795cee38faa82`；Git blob：`d7a62f959d7c575a40b0ed623956c71fa865e2fd`。
- 对象 SHA256：`2d8badb8b6ad1b53a465e979cd0ca6e53117f7ce7bfd6e8a326d51bca7d7cf96`。
- 组件状态：`PREVIOUSLY_ACCEPTED_EXACT_SOURCE`；新增根固定 SHA：pending。
- 编译：`PASS_STRICT_TRUST0`；[回执](history/round2/ledger-delivery/module-ledger.json)。
- 生产重放：`PASS_ORIGINAL_LEANCHECKER`；[回执](history/round2/ledger-delivery/module-ledger.json)。
- 公理审计：`PASS_OWNED_DECLARATIONS`；[回执](history/round2/ledger-delivery/module-ledger.json)。
- 声明：所属审计 18；pp.all 18；默认 pretty 0（有省略 0）。
- 未闭合输入：E1 geometry and saved-floor meaning；remaining adopted rows；full historical arithmetic parent licence；global union integral/coverage and no double count；all lower and upper integral ledger terms；two actual reserves；same actual rho density；full c, hLower and hUpper。

### ImbalancedChen.Certificates.RationalLogCertificate

- 文件：[ImbalancedChen/Certificates/RationalLogCertificate.lean](snapshot-sources/ImbalancedChen/Certificates/RationalLogCertificate.lean)；归属 **P2**；接收方：P2, P0。
- 当前证明源固定 SHA：`c9f407efe66240c08c2e8a678330ba7b98b74db5`；最新固定交接：`076473720210ee602e6e9735902e16bb6c5f1398`。
- 源码 SHA256：`4d705f561d4ba07e01dd7b3af1b0a73bcbf28c9dd6d2ddfd4ae288fb84de9d22`；Git blob：`354507bee23c4f7a8f3e463b6d3fda0f52db77c6`。
- 对象 SHA256：`4797bc0a53a1062592f29d0176efc6a9fb4c819ddf727ffbd43fe77504eaac3b`。
- 组件状态：`PREVIOUSLY_ACCEPTED_EXACT_SOURCE`；新增根固定 SHA：pending。
- 编译：`PASS_STRICT_TRUST0`；[回执](history/round2/ledger-delivery/module-ledger.json)。
- 生产重放：`PASS_ORIGINAL_LEANCHECKER`；[回执](history/round2/ledger-delivery/module-ledger.json)。
- 公理审计：`PASS_OWNED_DECLARATIONS`；[回执](history/round2/ledger-delivery/module-ledger.json)。
- 声明：所属审计 47；pp.all 47；默认 pretty 0（有省略 0）。
- 未闭合输入：E1 geometry and saved-floor meaning；remaining adopted rows；full historical arithmetic parent licence；global union integral/coverage and no double count；all lower and upper integral ledger terms；two actual reserves；same actual rho density；full c, hLower and hUpper。

### ImbalancedChen.Part3CurrentLowerDistribution

- 文件：[ImbalancedChen/Part3CurrentLowerDistribution.lean](snapshot-sources/ImbalancedChen/Part3CurrentLowerDistribution.lean)；归属 **P3**；接收方：P1, P5。
- 当前证明源固定 SHA：`64598da177adf861df3763d7c465ff941388b6d6`；最新固定交接：`f37f341412eb239f7e7e8937921ee8d01c9c2922`。
- 源码 SHA256：`a78bb4051c70e17d2b954d3c043af40754dfb1b37b0e42c60dd117c75a5c107d`；Git blob：`bd89bc32f6657d03a727adb4dcfccb9feaf4a52a`。
- 当前源未记录匹配已编译对象。
- 组件状态：`CANDIDATE`；新增根固定 SHA：pending。
- 编译：`NOT_RECORDED_CURRENT_SOURCE`；[回执](history/round2/ledger-delivery/module-ledger.json)。
- 生产重放：`NOT_RECORDED_CURRENT_SOURCE`；[回执](history/round2/ledger-delivery/module-ledger.json)。
- 公理审计：`NOT_RECORDED_CURRENT_SOURCE`；[回执](history/round2/ledger-delivery/module-ledger.json)。
- 声明：所属审计 未确认；pp.all 0；默认 pretty 0（有省略 0）。
- 未闭合输入：PrimeAPDistribution 及共享闭包后的本模块显式验证。；P1 实际模数 cap、实际选盒系数和行统一约束；P5 真实均值误差对接。。
- 待补验证：strict_compile, production_kernel_replay, owned_declaration_axiom_audit。

### ImbalancedChen.Part3DistributionTargets

- 文件：[ImbalancedChen/Part3DistributionTargets.lean](snapshot-sources/ImbalancedChen/Part3DistributionTargets.lean)；归属 **P3**；接收方：P1, P4-A, P4-B, P5。
- 当前证明源固定 SHA：`64598da177adf861df3763d7c465ff941388b6d6`；最新固定交接：`f37f341412eb239f7e7e8937921ee8d01c9c2922`。
- 源码 SHA256：`b11099467fa40c9975e4f76afb29cbff95923c81c3938b1b250769c62c1cb490`；Git blob：`30d4aa75c285fccae2f56562a26c6e2ecbf03fb4`。
- 当前源未记录匹配已编译对象。
- 组件状态：`CANDIDATE`；新增根固定 SHA：pending。
- 编译：`NOT_RECORDED_CURRENT_SOURCE`；[回执](history/round2/ledger-delivery/module-ledger.json)。
- 生产重放：`NOT_RECORDED_CURRENT_SOURCE`；[回执](history/round2/ledger-delivery/module-ledger.json)。
- 公理审计：`NOT_RECORDED_CURRENT_SOURCE`；[回执](history/round2/ledger-delivery/module-ledger.json)。
- 声明：所属审计 未确认；pp.all 0；默认 pretty 0（有省略 0）。
- 未闭合输入：显式验证依赖闭合。；实际完整模数范围的 medium/双长变量分布与所需 uniform rough/Möbius SW。。
- 待补验证：strict_compile, production_kernel_replay, owned_declaration_axiom_audit。

### ImbalancedChen.Part3LongSlotDistribution

- 文件：[ImbalancedChen/Part3LongSlotDistribution.lean](snapshot-sources/ImbalancedChen/Part3LongSlotDistribution.lean)；归属 **P3**；接收方：P3, P4-B, P5。
- 当前证明源固定 SHA：`6d1e5c4710a66f68fd101d0b40b5514bbbba4919`；最新固定交接：`f37f341412eb239f7e7e8937921ee8d01c9c2922`。
- 源码 SHA256：`67ccc48e6a4befadfd4b5639e2cdb4bd43e443b8f4eaf3086fe5a6c5fbd0023e`；Git blob：`13288c1122f26135644bbd2c04f731f993ffa058`。
- 对象 SHA256：`fd8cdcf5ac894e5b904f8bdc0e80506b16c23bb17bc1a568ea4a3a5b50b61816`。
- 组件状态：`PREVIOUSLY_ACCEPTED_EXACT_SOURCE`；新增根固定 SHA：pending。
- 编译：`PASS_STRICT_TRUST0`；[回执](history/round2/ledger-delivery/module-ledger.json)。
- 生产重放：`PASS_ORIGINAL_LEANCHECKER`；[回执](history/round2/ledger-delivery/module-ledger.json)。
- 公理审计：`PASS_OWNED_DECLARATIONS`；[回执](history/round2/ledger-delivery/module-ledger.json)。
- 声明：所属审计 35；pp.all 35；默认 pretty 0（有省略 0）。
- 未闭合输入：Actual rough/prime coefficients, phases and medium/two-long-variable distribution are not supplied.；Same-rho realPhysicalDistributionError and normalization adapters remain separate.。

### ImbalancedChen.Part3LongSlotNormalization

- 文件：[ImbalancedChen/Part3LongSlotNormalization.lean](snapshot-sources/ImbalancedChen/Part3LongSlotNormalization.lean)；归属 **P3**；接收方：P3, P4-B, P5。
- 当前证明源固定 SHA：`f37f341412eb239f7e7e8937921ee8d01c9c2922`；最新固定交接：`f37f341412eb239f7e7e8937921ee8d01c9c2922`。
- 源码 SHA256：`ca4e4d237bb4a5d21f72af3223001621902d6763d0b7ef1f423f532fd94f69fc`；Git blob：`3e9aa6a43744d43e38d705d754963dba53e657e6`。
- 对象 SHA256：`a74f51987d4e5ea037a2a9f9a5d9a74251ba7f697d4bede12f9252b9ef36a7e7`。
- 组件状态：`RECEIPT_ACCEPTED_PENDING_NEW_INTEGRATION_SHA`；新增根固定 SHA：pending。
- 编译：`PASS_REUSED_EXACT_SOURCE_AND_OBJECT`，exit=0，9.477 秒；[回执](../intake/p3-intake/P3_RECEIPT_REUSE.json)。
- 生产重放：`PASS_REUSED_EXACT_SOURCE_AND_OBJECT`，exit=0，2.785 秒；[回执](../intake/p3-intake/P3_RECEIPT_REUSE.json)。
- 公理审计：`PASS_REUSED_EXACT_SOURCE_AND_OBJECT`，exit=0，15.226 秒；[回执](../intake/p3-intake/P3_RECEIPT_REUSE.json)。
- 声明：所属审计 2；pp.all 2；默认 pretty 0（有省略 0）。
- 未闭合输入：归一化转移仍需其真实前提；物理 MD ≤ N^theta 不是本模块的新结论。；rough-prime / long-slot 分布、长区间、Brun–Mellin 及 medium/two-long 的全部算术供应尚待闭合。；本模块不供应同一实际 rho 的 K 密度界或 hUpper/hLower。。

### ImbalancedChen.Part3PrimeAPDistribution

- 文件：[ImbalancedChen/Part3PrimeAPDistribution.lean](snapshot-sources/ImbalancedChen/Part3PrimeAPDistribution.lean)；归属 **P3**；接收方：P3, P4-B, P5。
- 当前证明源固定 SHA：`7d70a2545fd819706e473eb41e4d430ad19119d8`；最新固定交接：`f37f341412eb239f7e7e8937921ee8d01c9c2922`。
- 源码 SHA256：`55319b7e1150799a5bd2ed4bcc0ef3dd486de57409d9b859f678c068bcb8c7fc`；Git blob：`2d761133b313302ab3a89ae906eb6944037a093d`。
- 当前源未记录匹配已编译对象。
- 组件状态：`CANDIDATE`；新增根固定 SHA：pending。
- 编译：`NOT_RECORDED_CURRENT_SOURCE`；[回执](history/round2/ledger-delivery/module-ledger.json)。
- 生产重放：`NOT_RECORDED_CURRENT_SOURCE`；[回执](history/round2/ledger-delivery/module-ledger.json)。
- 公理审计：`NOT_RECORDED_CURRENT_SOURCE`；[回执](history/round2/ledger-delivery/module-ledger.json)。
- 声明：所属审计 未确认；pp.all 0；默认 pretty 0（有省略 0）。
- 未闭合输入：7d70 固定更新仍为未编译候选，不能沿用旧源验证状态。；完整实际大模数分布并不由普通平方根 BV 取代。。
- 待补验证：strict_compile, production_kernel_replay, owned_declaration_axiom_audit。

### ImbalancedChen.Part3RoughAuxiliarySW

- 文件：[ImbalancedChen/Part3RoughAuxiliarySW.lean](snapshot-sources/ImbalancedChen/Part3RoughAuxiliarySW.lean)；归属 **P3**；接收方：P3, P4-B, P5。
- 当前证明源固定 SHA：`7d70a2545fd819706e473eb41e4d430ad19119d8`；最新固定交接：`f37f341412eb239f7e7e8937921ee8d01c9c2922`。
- 源码 SHA256：`d1ff2dc2e0ce6f9f5e18eb2b01da4ae10dfb42c23d2d49f1bb241f8c7796a9f8`；Git blob：`7ac03bfc01b00b228fb108bf1186ef45302b8344`。
- 当前源未记录匹配已编译对象。
- 组件状态：`CANDIDATE`；新增根固定 SHA：pending。
- 编译：`NOT_RECORDED_CURRENT_SOURCE`；[回执](history/round2/ledger-delivery/module-ledger.json)。
- 生产重放：`NOT_RECORDED_CURRENT_SOURCE`；[回执](history/round2/ledger-delivery/module-ledger.json)。
- 公理审计：`NOT_RECORDED_CURRENT_SOURCE`；[回执](history/round2/ledger-delivery/module-ledger.json)。
- 声明：所属审计 未确认；pp.all 0；默认 pretty 0（有省略 0）。
- 未闭合输入：7d70 新模块必须显式编译/重放/审计；29 个新证明体目前仅源码候选。；这给出 auxiliary-k 和大模数约化，尚非 k=1 的小模数实际 rough/Möbius SW，也不是 medium dispersion。。
- 待补验证：strict_compile, production_kernel_replay, owned_declaration_axiom_audit。

### ImbalancedChen.Part3RoughAuxiliarySWNormalization

- 文件：[ImbalancedChen/Part3RoughAuxiliarySWNormalization.lean](snapshot-sources/ImbalancedChen/Part3RoughAuxiliarySWNormalization.lean)；归属 **P3**；接收方：P3, P4-B, P5。
- 当前证明源固定 SHA：`7d70a2545fd819706e473eb41e4d430ad19119d8`；最新固定交接：`f37f341412eb239f7e7e8937921ee8d01c9c2922`。
- 源码 SHA256：`1d1a6e5d23449f3733a7532018ea23ae820bab06a8c45d46476cc9f2a6b7f91c`；Git blob：`60bd8f19aa6733851fbfc43b2afb269a97fa1ed3`。
- 当前源未记录匹配已编译对象。
- 组件状态：`CANDIDATE`；新增根固定 SHA：pending。
- 编译：`NOT_RECORDED_CURRENT_SOURCE`；[回执](history/round2/ledger-delivery/module-ledger.json)。
- 生产重放：`NOT_RECORDED_CURRENT_SOURCE`；[回执](history/round2/ledger-delivery/module-ledger.json)。
- 公理审计：`NOT_RECORDED_CURRENT_SOURCE`；[回执](history/round2/ledger-delivery/module-ledger.json)。
- 声明：所属审计 未确认；pp.all 0；默认 pretty 0（有省略 0）。
- 未闭合输入：7d70 新模块显式编译/重放/审计及前模块依赖。；实际 k=1 小模数 rough/Möbius uniform hSW 仍是明示未证输入，不能用封装宣称消除。；完整 medium (18)、碰撞范数 (23)、共同包 Kuznetsov/exceptional return (24) 与 theta=7/32 的真实解析证明仍缺。。
- 待补验证：strict_compile, production_kernel_replay, owned_declaration_axiom_audit。

### ImbalancedChen.ActualUpperDensityAssembly

- 文件：[ImbalancedChen/ActualUpperDensityAssembly.lean](snapshot-sources/ImbalancedChen/ActualUpperDensityAssembly.lean)；归属 **P4-A**；接收方：P4-B, P5。
- 当前证明源固定 SHA：`262f69822a386a9d44efc059bceba11049668d68`；最新固定交接：`3d5dd058cf6bef5fe90719ee277580baf8b5bf41`。
- 源码 SHA256：`241eaf65d39385e9f556a80184b25b0b2c2f67503922ec03f6a55b15c646ef3d`；Git blob：`80ec53545eeb91ccdc172d7072c6568c1dc01c5d`。
- 当前源未记录匹配已编译对象。
- 组件状态：`CANDIDATE`；新增根固定 SHA：pending。
- 编译：`NOT_REACHED_DEPENDENCY_BUILD_TIMEOUT`；[回执](../intake/p2-p4-intake/INTAKE.json)。
- 生产重放：`NOT_REACHED_DEPENDENCY_BUILD_TIMEOUT`；[回执](../intake/p2-p4-intake/INTAKE.json)。
- 公理审计：`NOT_REACHED_DEPENDENCY_BUILD_TIMEOUT`；[回执](../intake/p2-p4-intake/INTAKE.json)。
- 声明：所属审计 未确认；pp.all 0；默认 pretty 0（有省略 0）。
- 未闭合输入：actual causal policy and compiled rough coefficient；common-carrier zero extension；M times absolute reciprocal-totient compiler error；full actual policy integral and adopted numerical certificate；correct log D to log N coefficient conversion；one same rho for majorant density coprime correction and signed distribution；fixed b kappa sieveExponent before delta as required；actual K export to P5 independent of P4-B；actual hUpper supplier。
- 待补验证：explicit_production_compile, strict_trust0_compile, original_kernel_replay, all_owned_axiom_audit。

### ImbalancedChen.ActualUpperPolicyDensity

- 文件：[ImbalancedChen/ActualUpperPolicyDensity.lean](snapshot-sources/ImbalancedChen/ActualUpperPolicyDensity.lean)；归属 **P4-A**；接收方：P4-A, P4-B, P5。
- 当前证明源固定 SHA：`262f69822a386a9d44efc059bceba11049668d68`；最新固定交接：`3d5dd058cf6bef5fe90719ee277580baf8b5bf41`。
- 源码 SHA256：`16d81ee162d9ed2a5efad703c9a900b2c5ada622b2613472f70eaef4cbd02ae6`；Git blob：`487f13707ee13159cd7f161879b5a2e44ffb8c19`。
- 当前源未记录匹配已编译对象。
- 组件状态：`CANDIDATE`；新增根固定 SHA：pending。
- 编译：`NOT_REACHED_DEPENDENCY_BUILD_TIMEOUT`；[回执](../intake/p2-p4-intake/INTAKE.json)。
- 生产重放：`NOT_REACHED_DEPENDENCY_BUILD_TIMEOUT`；[回执](../intake/p2-p4-intake/INTAKE.json)。
- 公理审计：`NOT_REACHED_DEPENDENCY_BUILD_TIMEOUT`；[回执](../intake/p2-p4-intake/INTAKE.json)。
- 声明：所属审计 未确认；pp.all 0；默认 pretty 0（有省略 0）。
- 未闭合输入：actual causal policy and compiled rough coefficient；common-carrier zero extension；M times absolute reciprocal-totient compiler error；full actual policy integral and adopted numerical certificate；correct log D to log N coefficient conversion；one same rho for majorant density coprime correction and signed distribution；fixed b kappa sieveExponent before delta as required；actual K export to P5 independent of P4-B；actual hUpper supplier。
- 待补验证：explicit_production_compile, strict_trust0_compile, original_kernel_replay, all_owned_axiom_audit。

### ImbalancedChen.RealPhysicalUpperWeightBridge

- 文件：[ImbalancedChen/RealPhysicalUpperWeightBridge.lean](snapshot-sources/ImbalancedChen/RealPhysicalUpperWeightBridge.lean)；归属 **P4-B**；接收方：P4-B。
- 当前证明源固定 SHA：`262f69822a386a9d44efc059bceba11049668d68`；最新固定交接：`3d5dd058cf6bef5fe90719ee277580baf8b5bf41`。
- 源码 SHA256：`f82e567435a61125c6972da1f2c1430ff946bbd44bd9b5538bd9a6003382ea9d`；Git blob：`9fcdf562291c27cb75c8a102e6dcafddf1200905`。
- 当前源未记录匹配已编译对象。
- 组件状态：`CANDIDATE`；新增根固定 SHA：pending。
- 编译：`NOT_REACHED_DEPENDENCY_BUILD_TIMEOUT`；[回执](../intake/p2-p4-intake/INTAKE.json)。
- 生产重放：`NOT_REACHED_DEPENDENCY_BUILD_TIMEOUT`；[回执](../intake/p2-p4-intake/INTAKE.json)。
- 公理审计：`NOT_REACHED_DEPENDENCY_BUILD_TIMEOUT`；[回执](../intake/p2-p4-intake/INTAKE.json)。
- 声明：所属审计 未确认；pp.all 0；默认 pretty 0（有省略 0）。
- 未闭合输入：actual causal policy and compiled rough coefficient；common-carrier zero extension；M times absolute reciprocal-totient compiler error；full actual policy integral and adopted numerical certificate；correct log D to log N coefficient conversion；one same rho for majorant density coprime correction and signed distribution；fixed b kappa sieveExponent before delta as required；actual K export to P5 independent of P4-B；actual hUpper supplier。
- 待补验证：explicit_production_compile, strict_trust0_compile, original_kernel_replay, all_owned_axiom_audit。

### ImbalancedChen.RealUpperCountingAssembly

- 文件：[ImbalancedChen/RealUpperCountingAssembly.lean](snapshot-sources/ImbalancedChen/RealUpperCountingAssembly.lean)；归属 **P4-B**；接收方：P0。
- 当前证明源固定 SHA：`262f69822a386a9d44efc059bceba11049668d68`；最新固定交接：`3d5dd058cf6bef5fe90719ee277580baf8b5bf41`。
- 源码 SHA256：`56bab762d3f765f5080a441910a8696e297bcd72801e13f4338b0ed7142a9a96`；Git blob：`6e6843444cafa0e1d51a903981da0092983d2ac0`。
- 当前源未记录匹配已编译对象。
- 组件状态：`CANDIDATE`；新增根固定 SHA：pending。
- 编译：`NOT_REACHED_DEPENDENCY_BUILD_TIMEOUT`；[回执](../intake/p2-p4-intake/INTAKE.json)。
- 生产重放：`NOT_REACHED_DEPENDENCY_BUILD_TIMEOUT`；[回执](../intake/p2-p4-intake/INTAKE.json)。
- 公理审计：`NOT_REACHED_DEPENDENCY_BUILD_TIMEOUT`；[回执](../intake/p2-p4-intake/INTAKE.json)。
- 声明：所属审计 未确认；pp.all 0；默认 pretty 0（有省略 0）。
- 未闭合输入：actual causal policy and compiled rough coefficient；common-carrier zero extension；M times absolute reciprocal-totient compiler error；full actual policy integral and adopted numerical certificate；correct log D to log N coefficient conversion；one same rho for majorant density coprime correction and signed distribution；fixed b kappa sieveExponent before delta as required；actual K export to P5 independent of P4-B；actual hUpper supplier。
- 待补验证：explicit_production_compile, strict_trust0_compile, original_kernel_replay, all_owned_axiom_audit。

### ImbalancedChen.UpperCoefficientPerturbation

- 文件：[ImbalancedChen/UpperCoefficientPerturbation.lean](snapshot-sources/ImbalancedChen/UpperCoefficientPerturbation.lean)；归属 **P4-A**；接收方：P4-A, P4-B, P5。
- 当前证明源固定 SHA：`262f69822a386a9d44efc059bceba11049668d68`；最新固定交接：`3d5dd058cf6bef5fe90719ee277580baf8b5bf41`。
- 源码 SHA256：`59b45cfb13444beee297beec05b6d2153d7207db4f9bd96a8652260eaa57bcef`；Git blob：`498d09cf1bb960fc5cdd5d811e84f947a651bdc4`。
- 当前源未记录匹配已编译对象。
- 组件状态：`CANDIDATE`；新增根固定 SHA：pending。
- 编译：`NOT_REACHED_DEPENDENCY_BUILD_TIMEOUT`；[回执](../intake/p2-p4-intake/INTAKE.json)。
- 生产重放：`NOT_REACHED_DEPENDENCY_BUILD_TIMEOUT`；[回执](../intake/p2-p4-intake/INTAKE.json)。
- 公理审计：`NOT_REACHED_DEPENDENCY_BUILD_TIMEOUT`；[回执](../intake/p2-p4-intake/INTAKE.json)。
- 声明：所属审计 未确认；pp.all 0；默认 pretty 0（有省略 0）。
- 未闭合输入：actual causal policy and compiled rough coefficient；common-carrier zero extension；M times absolute reciprocal-totient compiler error；full actual policy integral and adopted numerical certificate；correct log D to log N coefficient conversion；one same rho for majorant density coprime correction and signed distribution；fixed b kappa sieveExponent before delta as required；actual K export to P5 independent of P4-B；actual hUpper supplier。
- 待补验证：explicit_production_compile, strict_trust0_compile, original_kernel_replay, all_owned_axiom_audit。

### ImbalancedChen.CurrentChenBuchstabRefinement

- 文件：[ImbalancedChen/CurrentChenBuchstabRefinement.lean](snapshot-sources/ImbalancedChen/CurrentChenBuchstabRefinement.lean)；归属 **P5**；接收方：P2, P5, P0。
- 当前证明源固定 SHA：`db97d0fe03250f4d9a8aea34b23e9c20f67010b8`；最新固定交接：`bf54caeb5e708474cacefac13a171d307b4c64f2`。
- 源码 SHA256：`02e565bf35ecff746ce3d552b64bc0cad3a402aecfd1484c1e9d4a967f159ca5`；Git blob：`303e0fe8ffbb46c53e4a53698a3662c9c207092f`。
- 对象 SHA256：`33663881df095e9bebdc3ea62b466da55da6cb8e33d1d73985c0053792162980`。
- 组件状态：`PREVIOUSLY_ACCEPTED_EXACT_SOURCE`；新增根固定 SHA：pending。
- 编译：`PASS_STRICT_TRUST0`；[回执](history/round2/ledger-delivery/module-ledger.json)。
- 生产重放：`PASS_ORIGINAL_LEANCHECKER`；[回执](history/round2/ledger-delivery/module-ledger.json)。
- 公理审计：`PASS_FIVE_OWNED_DECLARATIONS`；[回执](history/round2/ledger-delivery/module-ledger.json)。
- 声明：所属审计 5；pp.all 5；默认 pretty 0（有省略 0）。
- 未闭合输入：No adopted L1 identification；No complete eleven-term analytic mean；No actual common-rho K density supplier；No final hLower；P5 waits on P4-A, not P4-B。

### ImbalancedChen.CurrentChenLowerScale

- 文件：[ImbalancedChen/CurrentChenLowerScale.lean](snapshot-sources/ImbalancedChen/CurrentChenLowerScale.lean)；归属 **P5**；接收方：P5, P0。
- 当前证明源固定 SHA：`bd83a110ee52626daf9e68535c007eb73a93daca`；最新固定交接：`bf54caeb5e708474cacefac13a171d307b4c64f2`。
- 源码 SHA256：`cea233e4897e4f550760ca82eba84e6ca9254593a8cbba030f22940e3086ab13`；Git blob：`7f13b7bc1d89bae22b5936aaedce1b39c2fefc30`。
- 对象 SHA256：`7d1f14794fe5c19328247b3f713f530e106076fd9fba3ea860884c6915a3ed9a`。
- 组件状态：`PREVIOUSLY_ACCEPTED_EXACT_SOURCE`；新增根固定 SHA：pending。
- 编译：`PASS_STRICT_TRUST0`；[回执](history/round2/ledger-delivery/module-ledger.json)。
- 生产重放：`PASS_ORIGINAL_LEANCHECKER`；[回执](history/round2/ledger-delivery/module-ledger.json)。
- 公理审计：`PASS_OWNED_DECLARATIONS`；[回执](history/round2/ledger-delivery/module-ledger.json)。
- 声明：所属审计 5；pp.all 5；默认 pretty 0（有省略 0）。
- 未闭合输入：No adopted L1 identification；No complete eleven-term analytic mean；No actual common-rho K density supplier；No final hLower；P5 waits on P4-A, not P4-B。

### ImbalancedChen.CurrentChenMeanLedger

- 文件：[ImbalancedChen/CurrentChenMeanLedger.lean](snapshot-sources/ImbalancedChen/CurrentChenMeanLedger.lean)；归属 **P5**；接收方：P5, P0。
- 当前证明源固定 SHA：`bd83a110ee52626daf9e68535c007eb73a93daca`；最新固定交接：`bf54caeb5e708474cacefac13a171d307b4c64f2`。
- 源码 SHA256：`30597d5f381031fc7d7e794fe105a11d6981053b34a1406d46f40bf7840dc0c8`；Git blob：`59e259fd376660af2a6209b00a68ed83794a3b87`。
- 对象 SHA256：`1ddb7c1f850ad945ea093de5f98930e606654d286b7de19359df7c77c784cb9d`。
- 组件状态：`PREVIOUSLY_ACCEPTED_EXACT_SOURCE`；新增根固定 SHA：pending。
- 编译：`PASS_STRICT_TRUST0`；[回执](history/round2/ledger-delivery/module-ledger.json)。
- 生产重放：`PASS_ORIGINAL_LEANCHECKER`；[回执](history/round2/ledger-delivery/module-ledger.json)。
- 公理审计：`PASS_OWNED_DECLARATIONS`；[回执](history/round2/ledger-delivery/module-ledger.json)。
- 声明：所属审计 93；pp.all 93；默认 pretty 0（有省略 0）。
- 未闭合输入：No adopted L1 identification；No complete eleven-term analytic mean；No actual common-rho K density supplier；No final hLower；P5 waits on P4-A, not P4-B。

### ImbalancedChen.CurrentPairedBuchstabBridge

- 文件：[ImbalancedChen/CurrentPairedBuchstabBridge.lean](snapshot-sources/ImbalancedChen/CurrentPairedBuchstabBridge.lean)；归属 **P0**；接收方：P2, P5, P0。
- 当前证明源固定 SHA：`c9f407efe66240c08c2e8a678330ba7b98b74db5`；最新固定交接：`cce2334906f068fda2f58c400646366f2aa2d417`。
- 源码 SHA256：`280481d294ebd6c9fa73e74e19b5dbd2efcb2018af6c6a1953d746cee80a7550`；Git blob：`6db112740c1a5ac1981dbe5d0e6705e718382296`。
- 对象 SHA256：`c8417cc4c39232255658008db80468d38df39cf68536d865c17f07cd46bd81dd`。
- 组件状态：`PREVIOUSLY_ACCEPTED_EXACT_SOURCE`；新增根固定 SHA：pending。
- 编译：`PASS_STRICT_TRUST0`；[回执](history/round2/ledger-delivery/module-ledger.json)。
- 生产重放：`PASS_ORIGINAL_LEANCHECKER`；[回执](history/round2/ledger-delivery/module-ledger.json)。
- 公理审计：`PASS_OWNED_DECLARATIONS`；[回执](history/round2/ledger-delivery/module-ledger.json)。
- 声明：所属审计 2；pp.all 2；默认 pretty 0（有省略 0）。
- 未闭合输入：The entire adopted mask and the real arithmetic parent remain separate inputs.；The integral coefficient K/80 already contains the gain 1/20 times K/4; do not apply that gain twice.；No full K/c/hLower/hUpper claim.。

### ImbalancedChen.CurrentChenInitialSource

- 文件：[ImbalancedChen/CurrentChenInitialSource.lean](snapshot-sources/ImbalancedChen/CurrentChenInitialSource.lean)；归属 **P5**；接收方：P5, P0。
- 当前证明源固定 SHA：`bf54caeb5e708474cacefac13a171d307b4c64f2`；最新固定交接：`bf54caeb5e708474cacefac13a171d307b4c64f2`。
- 源码 SHA256：`4b11a63cc976a0866068337c12d616578dace6c80736574311f4cca13f7d8956`；Git blob：`147da5cdb46787f2befe7e21856fd4691190d0ac`。
- 对象 SHA256：`8b9ee7b0e4f18ea06057a99f075e87065131e12873221e114b9c5d5c46a8ef39`。
- 组件状态：`CANDIDATE_LEGACY_AUDIT_IMPORT_BINDING_PENDING`；新增根固定 SHA：pending。
- 编译：`PRODUCER_PASS_LEGACY_BINDING_INCOMPLETE`，exit=0，258.283 秒；[回执](../intake/p5-intake/p5-fixed-intake.json)。
- 生产重放：`PRODUCER_PASS_LEGACY_BINDING_INCOMPLETE`，exit=0，210.823 秒；[回执](../intake/p5-intake/p5-fixed-intake.json)。
- 公理审计：`PRODUCER_PASS_LEGACY_BINDING_INCOMPLETE`，exit=0，680.789 秒；[回执](../intake/p5-intake/p5-fixed-intake.json)。
- 声明：所属审计 8；pp.all 0；默认 pretty 8（有省略 0）。
- 未闭合输入：Producer legacy audit has no before/after imported target object capture. Do not invent fields.；No adopted L1 identification；No complete eleven-term analytic mean；No actual common-rho K density supplier；No final hLower；P5 waits on P4-A, not P4-B。
- 待补验证：P0_exact_import_bound_owned_audit, full_replay_target_lineage_binding_for_legacy_schema。

### ImbalancedChen.CurrentChenInitialMean

- 文件：[ImbalancedChen/CurrentChenInitialMean.lean](snapshot-sources/ImbalancedChen/CurrentChenInitialMean.lean)；归属 **P5**；接收方：P5, P0。
- 当前证明源固定 SHA：`bf54caeb5e708474cacefac13a171d307b4c64f2`；最新固定交接：`bf54caeb5e708474cacefac13a171d307b4c64f2`。
- 源码 SHA256：`5358e4dbbda436b335620de19884624df3260386d5ab5e478a85f70599da6137`；Git blob：`6f88af462172d9f3fbef9cc68bf3cfce052ec88a`。
- 当前源未记录匹配已编译对象。
- 组件状态：`SOURCE_CANDIDATE_NOT_LEAN_VERIFIED`；新增根固定 SHA：pending。
- 编译：`NOT_RECORDED_CURRENT_FIXED_SOURCE`；[回执](../intake/p5-intake/p5-fixed-intake.json)。
- 生产重放：`NOT_RECORDED_CURRENT_FIXED_SOURCE`；[回执](../intake/p5-intake/p5-fixed-intake.json)。
- 公理审计：`NOT_RECORDED_CURRENT_FIXED_SOURCE`；[回执](../intake/p5-intake/p5-fixed-intake.json)。
- 声明：所属审计 未确认；pp.all 0；默认 pretty 0（有省略 0）。
- 未闭合输入：固定 S1BetaFixedNormalizedLower 供应链及当前 InitialMean 源尚无完成的匹配验证。；No adopted L1 identification；No complete eleven-term analytic mean；No actual common-rho K density supplier；No final hLower；P5 waits on P4-A, not P4-B。
- 待补验证：compile_supplier_closure, strict_trust0_compile, original_kernel_replay, all_owned_axiom_audit。

### ImbalancedChen.Certificates.PairedV2Geometry

- 文件：[ImbalancedChen/Certificates/PairedV2Geometry.lean](snapshot-sources/ImbalancedChen/Certificates/PairedV2Geometry.lean)；归属 **P2**；接收方：P1, P2, P5, P0。
- 当前证明源固定 SHA：`6acf61cc28f227a9154363f2347c386ec01dffb0`；最新固定交接：`076473720210ee602e6e9735902e16bb6c5f1398`。
- 源码 SHA256：`68b17d29089e7a761428ff92957a7f8fbe9a4b3bff8105846717162867359238`；Git blob：`f7bb75a4a2c1b4debc41a334df30d64bf81647f5`。
- 对象 SHA256：`97383a88879ade52298b58954f6e825d97e17ab4d964e9a3ea57eb51fabd72fd`。
- 组件状态：`RECEIPT_ACCEPTED_PENDING_NEW_INTEGRATION_SHA`；新增根固定 SHA：pending。
- 编译：`PASS_REUSED_ACTUAL_FIXED_SOURCE_EXECUTION`，exit=0，4.919 秒；[回执](../../../../part2/round2/prefix4/gates/20261012T093452834277Z-compile-ImbalancedChen.Certificates.PairedV2Geometry.json)。
- 生产重放：`PASS_REUSED_ACTUAL_FIXED_SOURCE_EXECUTION`，exit=0，3.16 秒；[回执](../../../../part2/round2/prefix4/gates/20261012T094124096550Z-replay-ImbalancedChen.Certificates.PairedV2Geometry.json)。
- 公理审计：`PASS_EXACT_OBJECT_COMPLETE_DECLARATIONS`，exit=0，62.203 秒；[回执](../../../../part2/round2/prefix4/gates/20261012T094220468494Z-compile-verification.part2.CertificateAudit.json)。
- 声明：所属审计 10；pp.all 10；默认 pretty 0（有省略 0）。
- 未闭合输入：E1 geometry and saved-floor meaning；remaining adopted rows；full historical arithmetic parent licence；global union integral/coverage and no double count；all lower and upper integral ledger terms；two actual reserves；same actual rho density；full c, hLower and hUpper。

### ImbalancedChen.Certificates.PairedV2Prefix4Data

- 文件：[ImbalancedChen/Certificates/PairedV2Prefix4Data.lean](snapshot-sources/ImbalancedChen/Certificates/PairedV2Prefix4Data.lean)；归属 **P2**；接收方：P1, P2, P5, P0。
- 当前证明源固定 SHA：`6acf61cc28f227a9154363f2347c386ec01dffb0`；最新固定交接：`076473720210ee602e6e9735902e16bb6c5f1398`。
- 源码 SHA256：`25ffbba57b5fdff9ce23290ade00fbeaa2b38c2e44ffe9e8637404c8287aab2c`；Git blob：`3bfedf4c0c6222adb6afa747b2a4c394de841bc5`。
- 对象 SHA256：`41dc48727c4e788c9f5518c6acdf7d8590cc9dca761955ec92eba171d9c8eee0`。
- 组件状态：`RECEIPT_ACCEPTED_PENDING_NEW_INTEGRATION_SHA`；新增根固定 SHA：pending。
- 编译：`PASS_REUSED_ACTUAL_FIXED_SOURCE_EXECUTION`，exit=0，3.696 秒；[回执](../../../../part2/round2/prefix4/gates/20261012T093830454829Z-compile-ImbalancedChen.Certificates.PairedV2Prefix4Data.json)。
- 生产重放：`PASS_REUSED_ACTUAL_FIXED_SOURCE_EXECUTION`，exit=0，3.105 秒；[回执](../../../../part2/round2/prefix4/gates/20261012T094148133887Z-replay-ImbalancedChen.Certificates.PairedV2Prefix4Data.json)。
- 公理审计：`PASS_EXACT_OBJECT_COMPLETE_DECLARATIONS`，exit=0，62.203 秒；[回执](../../../../part2/round2/prefix4/gates/20261012T094220468494Z-compile-verification.part2.CertificateAudit.json)。
- 声明：所属审计 11；pp.all 11；默认 pretty 0（有省略 0）。
- 未闭合输入：E1 geometry and saved-floor meaning；remaining adopted rows；full historical arithmetic parent licence；global union integral/coverage and no double count；all lower and upper integral ledger terms；two actual reserves；same actual rho density；full c, hLower and hUpper。

### ImbalancedChen.Certificates.PairedV2Prefix4

- 文件：[ImbalancedChen/Certificates/PairedV2Prefix4.lean](snapshot-sources/ImbalancedChen/Certificates/PairedV2Prefix4.lean)；归属 **P2**；接收方：P1, P2, P5, P0。
- 当前证明源固定 SHA：`6acf61cc28f227a9154363f2347c386ec01dffb0`；最新固定交接：`076473720210ee602e6e9735902e16bb6c5f1398`。
- 源码 SHA256：`dc57cd323ba3cad0ca4b0d29d2c0839b4c0d90a87d7f27b497eac51587295395`；Git blob：`40dfff1c63af27d15da9f22e88b4b11e96369672`。
- 对象 SHA256：`2d90266fee10f47d425bb18c80be306fe4a33b9e9bc8aaedbff93fbd2558af45`。
- 组件状态：`RECEIPT_ACCEPTED_PENDING_NEW_INTEGRATION_SHA`；新增根固定 SHA：pending。
- 编译：`PASS_REUSED_ACTUAL_FIXED_SOURCE_EXECUTION`，exit=0，7.675 秒；[回执](../../../../part2/round2/prefix4/gates/20261012T094022452360Z-compile-ImbalancedChen.Certificates.PairedV2Prefix4.json)。
- 生产重放：`PASS_REUSED_ACTUAL_FIXED_SOURCE_EXECUTION`，exit=0，3.496 秒；[回执](../../../../part2/round2/prefix4/gates/20261012T094214084191Z-replay-ImbalancedChen.Certificates.PairedV2Prefix4.json)。
- 公理审计：`PASS_EXACT_OBJECT_COMPLETE_DECLARATIONS`，exit=0，62.203 秒；[回执](../../../../part2/round2/prefix4/gates/20261012T094220468494Z-compile-verification.part2.CertificateAudit.json)。
- 声明：所属审计 35；pp.all 35；默认 pretty 0（有省略 0）。
- 未闭合输入：E1 geometry and saved-floor meaning；remaining adopted rows；full historical arithmetic parent licence；global union integral/coverage and no double count；all lower and upper integral ledger terms；two actual reserves；same actual rho density；full c, hLower and hUpper。

## 采用证书与接口边界

P2 Prefix4 只覆盖采用 v2 corpus 的原始零基编号 **0–3，E0**，包含此前首格。结果是四个已绑定实际格积分的有限和区间；没有把全部 17572 行、E1、全历史许可、全局并集积分或误差账本标为已证。

四格有限积分和：`12676565261567/100000000000000000000` ≤ sum ≤ `12676572571081/100000000000000000000`。采用 corpus SHA256：`f6d31386f93cf77888ea4771ffa549a1cf61dca700bac618ff7646566a02f9b7`。原 Q160 区间没有成为未经证明的前提。

`K / 80` 已含 `(1 / 20) * (K / 4)` 的增益；不能再乘一次增益。固定常数、实际权、计数、归一化、实数参数及量词保持原定义；有限局部通过不等于实际 K 或 c 的完整解析证明。

| 供应关系 | 本批状态 |
| --- | --- |
| P5 → P2 Buchstab | 已接收 Buchstab refinement 与 P0 配对桥，继续复用 |
| P1 → P2 / P4-A / P5 实际构造 | 四个局部生产模块接收；完整采用历史、合法性/支持、真实全局积分仍未闭合 |
| P3 → P4 / P5 分布 | LongSlot 与 Normalization 接收；其余实际分布及误差供应仍缺 |
| P4-A → P5 同一实际 rho 的 K | 尚待真实供应；**P5 不必等 P4-B** |
| P4-B → P0 hUpper | 尚待真实供应 |
| P5 → P0 十一项均值、c、hLower | 尚待真实供应 |

## 单列的上游与候选

S1Carrier 属于固定 goldbach 依赖 `09b97db5764ade1246bfb77206baa1b124760958`，源码 SHA256 `757bdcea11195c48ed5814f95a70737326853e68bfaa093711a4f6161e1a896a`。已有真实 strict/replay/audit，36 个所属声明审计与 17 个完整 public pp.all/Expr 类型可复用。两条 generated 默认类型有省略，不能称 36 条完整类型。该上游模块不计入 31 / 19 / 591。见 [上游类型](upstream-S1Carrier-types.json)。

P5 InitialSource 的旧 `2573e5…` 源真实失败保留；当前 `4b11a6…` 修复已固定且 producer 三门确实成功。旧 schema 缺 audit 导入对象前后绑定，故暂不列为组件接收。InitialMean 当前 `5358e4…` 固定源仍待供应链及模块验证；类型只按源码提取。其 S1 局部下界尚不等于采用 L1、完整十一项均值、c 或 hLower。

P1 取得以下两份未提交 joint-cell 第五层候选，固定 commit 都为 null，当前没有匹配对象回执；两份均独立保存源码身份。它们尚未与用户先前报告的“独立全局第五层积分仅单模块编译”候选建立身份对应。保留已取得成果，同时保留原候选的定位缺口。

| 候选源码 | SHA256 | 固定提交 / 编译器确认 |
| --- | --- | --- |
| [ImbalancedChen/HistoricalUpperFiveCellGeometry.lean](unfixed-candidate-sources/ImbalancedChen/HistoricalUpperFiveCellGeometry.lean) | `0d54b930393ef01dbc9c44fbec5f356bf6be9a645a1a537064179fc12799424b` | null / 无 |
| [ImbalancedChen/ActualHistoricalFifthCellIntegral.lean](unfixed-candidate-sources/ImbalancedChen/ActualHistoricalFifthCellIntegral.lean) | `dd9afad8cae4c977b8c6916e12ac38d0c4edeb5f7b1e0d42768958bae30f031a` | null / 无 |

## 首诊断与历史不可改写

原 P1 接收器把两个首诊断误截成 `/`。本候选从其原始日志恢复完整行和完整诊断块：[CORRECTED_INTAKE_DIAGNOSTICS.json](CORRECTED_INTAKE_DIAGNOSTICS.json)。这是一项接收器提取字段修正，**不是新生产证明失败**。

- attempt-01：Part1HistoryAudit 首个错误为缺少 LevelCheckProbe.olean。
- attempt-02：LevelCheckProbe 首个错误为 `decide` 无法归约 `increasing.levelCheck = true`。
- P5 原 S1Carrier exit 130 按中断保存，不改写成 Lean 证明失败；其后成功是另一条实际记录。
- P4 专用 CI 在依赖构建处超时，五目标完成数为 0；不伪造第一处 Lean 诊断。

上轮完整 28 模块记录及配套文件逐字节保存在 [历史台账](history/round2/ledger-delivery/module-ledger.json)，历史文件 SHA256 `fbc89d287e58d693b09bb1b53cbe1b4468992754389ec6c1863031e8a2aa8e73`。原编译失败不随当前源升格而删除，也不把旧失败迁移到新源。

## 复建

以下命令只读取现有固定源码、Git 对象和已下载回执，写新台账；不调用 Lean、Lake、CI 或 Codex。路径可替换。

```bash
python build_ledger.py \
  --round-root /workspace/scratch/535d89efd063/p0-round3 \
  --previous-ledger /workspace/scratch/535d89efd063/p0-round3/previous-ledger/ledger-delivery/module-ledger.json \
  --git-repo /workspace/scratch/535d89efd063/goldbach-formalization \
  --output-dir /workspace/scratch/535d89efd063/p0-round3/ledger-candidate
```

此候选的角色是可追溯组件接收台账。完整最终入口仍须调用真正已证的上下界，最终类型不得携带 hLower、hUpper 或等价未证包装；新固定集成 SHA 的构建、内核及公理门保持待办。
