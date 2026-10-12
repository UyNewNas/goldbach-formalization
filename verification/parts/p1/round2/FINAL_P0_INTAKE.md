# P1 round 2 最终 P0 增量接收核对

## 结论与观察时间

**P0 已在 `28fd630ef7cc38eba86beb6c0ba123336b5d05f2` 正式接收 P1 的 `b09d5361e0b30f3e85cb912a03c7bfb85a99bf8f` 四个生产模块，并加入公共根导入。** 因而本目录早先 `UPSTREAM_INTAKE.md` / `upstream-intake.json` 在旧 P0 快照上记录的“接收仍停留于 70ad”只保留为历史状态，不再描述当前接收结果。[P0 接收回执][p1-intake]与[固定接收文件单][accept-files]明确列出 b09 的来源身份。

本次只读核对时间为 **2026-10-12 13:10:38–13:15:27 UTC**；分支 ref 与 exact-SHA CI 的回读在 13:14–13:15 UTC 完成。范围仅为下述一个增量提交、相关交接与源文件，以及该 SHA 的 Actions 元数据。本次没有运行 Lean、测试、checker、CI 或 Codex，没有修改生产源码、公共根、既有交接或外部分支。

| 身份 | 完整值 |
| --- | --- |
| 分支 | `chatgpt/chen-p0-integration` |
| 前次固定 P0 头 / 此次唯一父提交 | `cce2334906f068fda2f58c400646366f2aa2d417` |
| 本次实际读回 P0 头 | `28fd630ef7cc38eba86beb6c0ba123336b5d05f2` |
| 新树 | `0c72ea1ceff699e58a728cf0ae5714609d55b617` |
| 提交时间 | `2026-10-12T12:38:15Z` |
| 提交标题 | `Integrate eight verified Chen components and bind complete root checks` |
| 共同数学证明基线，保持不变 | `1a80c1bcce67886f699d097fc37fd245cd3620bf` |
| 手稿基线，保持不变 | `ba6ec11d800eccc54406490631895e174de85766` |
| P1 被接收的证明提交 | `b09d5361e0b30f3e85cb912a03c7bfb85a99bf8f` |
| P1 本轮原提交父头；相对 b09 仅外部 CI 时限调整 | `7f894bfb57b7aa561360e335c6d610b7c30614e0` |

[Git ref][ref]、[Git commit][commit]和[两 SHA compare][compare]相符：ahead 1、behind 0、唯一父提交为 cce。Compare 接口返回 300 个文件条目，存在接口数量上限；本记录不将它称为完整文件差异清单。新增生产范围另以[完整发布输入 manifest][publication]、实际公共根和四份 P1 生产文件读回交叉核对。

## 1. 接收内容与固定基线

新增生产模块为八个：P1 四个、P2 三个、P3 一个。P0 发布记录计本批 **198 个生产所属声明**；不是将 P1 的 Probe 算进生产声明。[P0 round-3 验证说明][round3]

| 来源 | 实际新增生产路径，均相对于 `ImbalancedChen/` |
| --- | --- |
| P1 | `OrdinaryLowerFourFrontier.lean`、`ActualSelectedPrefixLowerCellSum.lean`、`ActualSelectedPrefixLowerOwnCubeIntegral.lean`、`HistoricalPrefixCertificate.lean` |
| P2 | `Certificates/PairedV2Geometry.lean`、`Certificates/PairedV2Prefix4Data.lean`、`Certificates/PairedV2Prefix4.lean` |
| P3 | `Part3LongSlotNormalization.lean` |

P0 [保护项记录][protected]明确保持 `lean-toolchain`、`lakefile.toml`、`lake-manifest.json`、`docs/CURRENT_MANUSCRIPT_MAP.md`、`docs/EXTERNAL_REUSE.md`、`CurrentMainTheorem.lean` 与 `CurrentNumericalTransfer.lean` 的共同基线字节；Lean 仍为 `leanprover/lean4:v4.33.0-rc1`，依赖 pin 未变。**28fd 是新增组件的集成头，没有宣布替换共同数学或手稿基线。** 本次没有重新审计全部基线文件。

以下四份生产源码已直接从 28fd 读取，重算 Git blob 与工具返回值一致，且 SHA256 与 b09 的 P0 接收文件单逐项一致。P0 接收过程中没有改写这些证明。

| P1 生产文件 | 28fd 中实际 Git blob | 源码 SHA256 | 生产所属声明 |
| --- | --- | --- | ---: |
| `OrdinaryLowerFourFrontier.lean` | `05f0e3758e0b6fa0cfa6b3002e9c61ce164489ae` | `97f5e3390d9c90a9598a7fa5fa1ede84c174da9497f23c88be6ea04ffb0bc9e8` | 27 |
| `ActualSelectedPrefixLowerCellSum.lean` | `64e73f036cd309512ea5513377cb0528e65ed524` | `48b9b1b50d1fec780378e61a5250971cf0f5222b12fcf04706ad357f90040714` | 9 |
| `ActualSelectedPrefixLowerOwnCubeIntegral.lean` | `6a535380f1bb4074e06ff8ce4180eaae63d2e9fe` | `c98fd3407d59f27cd140689de36f888cfd804130dc9787e3e60ea451b4e1dcd1` | 8 |
| `HistoricalPrefixCertificate.lean` | `9c5d05230b05f102f10cb8dd086942dfc665fa3f` | `b6ef2c6febc61e28ddf5bbeb5c02fd665e5266833df4cd1b5b2640481cb6e6f3` | 96 |

P1 原始验证范围仍为六目标 strict / trustLevel 0、六次原装 selected-module checker，以及五个 defining modules 的 **150 个声明 = 140 生产 + 10 Probe**。它是官方 Lake 调用 `Lean.Elab.runFrontend` 的实际记录；P0 接收回执没有将其改称 stock `lake build`。P0 复核并复用原归档，记录核对 2,196 成员、689 条本地编译记录和 1,350 条内部 import 对象连接；这些属于生产者旧回执的接收核对，不是本次 P1 新运行。[P0 接收回执][p1-intake]

原始归档 SHA256 为 `c56fc707d40ad255fd2d9c8b6c94dc7442c9c62b7238d833188b18cdf10f601d`，原 receipt SHA256 为 `2a23599ce539e7768a938e729b9beb7516210ff49221f6a8fd8a0938107765a1`。缺 Probe 对象、普通 `decide` 的原失败与最终 `decide +kernel` 修复仍按各自版本保留，不混入成功对象身份。

## 2. 第五层源码：已取得的快照与仍未对应的旧报告

P0 新提交确实增加了本轮两份历史 joint-cell 源码的文本归档。已直接读取下列 **28fd 固定 Git 文件**，重算其 blob 和 SHA256；它们与 P1 本轮 12:07:42 UTC 被观察到的两个源文件一致：

| 28fd 中的实际归档路径 | Git blob | 源码 SHA256 |
| --- | --- | --- |
| [`verification/parts/p0/round3/candidates/p1/HistoricalUpperFiveCellGeometry.lean.txt`][geometry] | `b02e701b6a4a43e6e94bbbdd894140d5439130bf` | `0d54b930393ef01dbc9c44fbec5f356bf6be9a645a1a537064179fc12799424b` |
| [`verification/parts/p0/round3/candidates/p1/ActualHistoricalFifthCellIntegral.lean.txt`][integral] | `763d1a622ba0d06ce029d148bc8bb48c9e259741` | `dd9afad8cae4c977b8c6916e12ac38d0c4edeb5f7b1e0d42768958bae30f031a` |

准确时间口径是：它们在 P0 12:07:42 的 intake 时还是 P1 未提交源；**现在文本归档已有固定提交 28fd**。这不产生同源编译回执，也不使其成为已接收生产模块。P0 原记录中的 `fixed_commit: null` / `object_present_at_intake: false` 描述的是当时观察，不应改写为当前 Git 中不存在这些文本。

其中实际源码含 `ImbalancedChen.HistoricalPrefixCapData.tendsto_fifthPrimeCorrection_ceil` 等目标，范围是历史共同 cell 上的实际 prime-tuple correction 积分。第一 cube 使用根 old，第三 cube 使用有效第三祖先，旧第五 residual 使用有效第四祖先，old/new own-cube 指示分别保留。它没有提供整个 retained-polynomial fifth density 的身份或完整采用 policy 的全局密度界。[源码快照][integral]、[P0 候选范围记录][fifth-scope]

**用户此前另行报告的“继承前层选择、仅过单模块编译”的独立第五层积分候选，仍为 bounded `SOURCE_PENDING`。** P0 明确把那一报告与上述两份本轮续作分开，尚未给出能相互对应的原提交、实际文件及原始同源验证回执。本次没有重新搜索全仓库、全部 PR 历史、其他会话或不可访问成果；因此不声称该旧候选不存在。[候选快照身份记录][live-fifth]

P0 新公共根只增加前节八个生产导入，未导入这两份 joint-cell 候选，也没有导入 P1 本轮独立 `StoredHistoricalBoxPermit`。下节新根 CI 的成功不为它们提供编译或接收结果；P1 permit 的独立真实回执仍使用自己的三目标和 36 声明范围。

## 3. 发布时 pending 与最新实际 CI 状态

[P0 发布 manifest][publication]的 `PENDING_AT_PUBLICATION`、round-3 文档中的新根 pending，均为其发布时状态。**本次 exact-SHA Actions 回读已经看到 28fd 的两个 workflow completed / success。** 不能继续用发布时 pending 描述 13:15 UTC 的 Actions 结果。

| actual head SHA 均为 `28fd630ef7cc38eba86beb6c0ba123336b5d05f2` | 实际元数据结果 |
| --- | --- |
| [Core run 38250288277][core-run] | `completed / success`；创建 `12:38:28Z`，最后更新 `12:55:54Z` |
| [Core job 114814517789][core-job] | `completed / success`；`12:38:32Z–12:55:53Z` |
| [Variable envelope run 38250288172][ve-run] | `completed / success`；创建 `12:38:28Z`，最后更新 `12:41:31Z` |

Core job API 逐步骤实际状态：

| 步骤 | 状态 | 起止时间 UTC |
| --- | --- | --- |
| Build the full project | completed / success | 12:40:04–12:40:39 |
| Recheck ImbalancedChen with bundled Lean 4.33.0-rc1 leanchecker | completed / success | 12:40:39–12:46:44 |
| Audit ImbalancedChen root declarations and transitive axioms | completed / success | 12:46:44–12:47:09 |
| Export complete round 3 types and the existing conditional main bridge | completed / success | 12:47:09–12:55:03 |
| Record required verification outcomes | completed / success | 12:55:03–12:55:03 |

同时读回的[实际 workflow][workflow]保留 job 150 分钟、full build 90 分钟；新增 round-3 类型导出步骤及要求成功的 outcome 检查，调用 `verification/parts/p0/check_round3_types.py --timeout-seconds 540`。该 workflow 改动由 P0 发布，不是本次 P1 修改。

Core 当前公开 artifact 元数据为：`lean-verification-38250288277-1`，ID `11749070720`，230,630 bytes，未过期，digest `sha256:6927d09d7e2b4cd7dd201f21169c07111ff4325f77478682f5c316f551940e42`。[artifact 元数据][artifacts]

**本次只读取 run/job/step/artifact 元数据与固定 workflow，没有下载该 artifact 或读取其原始编译器输出。** 因此这里不宣称独立逐项核对了 28fd 的新根声明数、198 项完整类型或实际对象哈希，也不将旧 cce 根的 9,790 jobs / 5,260 声明数迁移给新根。已有 b09 六目标回执继续作为 P1 四模块逐对象验证依据；新 CI 元数据则准确登记在它自己的完整 SHA。原装 checker 的 selected-module 范围亦不被描述为重新重放全部导入依赖。

## 4. 对 P1 的接收与下一步约束

P0 现已接收普通 lower-fourth 的实际加权素数和、真实积分与 density restoration，以及有限历史 cap 的共同网格、祖先 fallback、有限 level check 和实际 upper telescope；这些组件的范围未被 P0 扩大为完整 boxed support 或采用政策的全局密度。

P2 Prefix4 仍只闭合原始行 0–3 / E0，含此前首格，不能再次计入首格收益；`K/80` 已含 `(K/4) × (1/20)`，不能重复支付增益。剩余行、E1、历史父许可、全域覆盖及不重计仍是后续输入。P3 新 normalization 两定理只供应零相位、未附 rough/prime 筛选的整数 long slot。P5 S1Carrier 36 声明是固定依赖的单列验证结果，不是本批新增 P0 生产模块，也不是第五层积分。[P0 round-3 验证说明][round3]

P1 本轮继续按自己的实际 receipt 交付独立 stored-cap permit；共同 cell / 实际 fifth prime correction 的主四目标状态不由 P0 此次接收或其根 CI 改写。完整 adopted historical construction、retained saving 身份、boxed physical rho、support/factorization、分布与截断误差、K/c/hLower/hUpper 仍须各自真实供应。

## 5. 可追溯来源与公共根快照

本次直接读回的 [`ImbalancedChen.lean`][root-source] 为 12,114 bytes，Git blob `a064bd2e42a4cd0297452d04d3bf213a085c8d4b`，SHA256 `e8226c047883a6176a608e425abd1601f1fc1d3422783f4cd7d2950081c94689`。它的最后八条导入恰为第一节八个新增生产模块。

关键文档的实际 Git blob：

| 来源 | Git blob |
| --- | --- |
| `docs/PART0_ROUND3_VERIFICATION.md` | `01253f99b667e4d57b1671aa68fc9509dfbf6cad` |
| `verification/parts/p0/round3/intake/p1-intake/P1_INTAKE.md` | `59869cc6ddeccb2def8a0548a60e0ed3c7d931cf` |
| `verification/parts/p0/round3/intake/p1-intake/P1_ACCEPT_FILES.json` | `b19ab69346f13485e9c89f912d558a0dcd6c765e` |
| `verification/parts/p0/round3/intake/p1-intake/FIFTH_CANDIDATE_SCOPE.json` | `d4ff6a5cb19dd53ff6e3dac806e78451ffeedcfe` |
| `verification/parts/p0/round3/intake/p1-intake/LIVE_FIFTH_CANDIDATES.json` | `fd23f2faf5c82856709106d99b602ddbd12035ce` |
| `verification/parts/p0/round3/PUBLICATION_MANIFEST.json` | `6c21d519303ea1b157c2505f9590dc2da5445090` |

原始 connector 结构化响应、所读源码内容与逐文件本地重算 hash 保存在本次 scratch `/workspace/scratch/127408f63891/p1-final-p0-intake/`。其中 `responses.json` 为 489,329 bytes，SHA256 `e7ff4f2e7f8aad1eec00df05e3ec7423cd71a65466b824dcd432f8fbf07ba0b0`；`source-bindings.json` 记录所有 16 份源/文档的 blob、SHA256、bytes 和固定 URL。`ImbalancedChen.at-28fd.lean.txt` 是字节精确的公共根快照，供 P0 增量导入补丁使用。Scratch 是本次追溯辅助；下列固定 GitHub 来源仍是持久的引用身份。

[ref]: https://api.github.com/repos/UyNewNas/goldbach-formalization/git/ref/heads/chatgpt/chen-p0-integration
[commit]: https://github.com/UyNewNas/goldbach-formalization/commit/28fd630ef7cc38eba86beb6c0ba123336b5d05f2
[compare]: https://github.com/UyNewNas/goldbach-formalization/compare/cce2334906f068fda2f58c400646366f2aa2d417...28fd630ef7cc38eba86beb6c0ba123336b5d05f2
[round3]: https://github.com/UyNewNas/goldbach-formalization/blob/28fd630ef7cc38eba86beb6c0ba123336b5d05f2/docs/PART0_ROUND3_VERIFICATION.md
[p1-intake]: https://github.com/UyNewNas/goldbach-formalization/blob/28fd630ef7cc38eba86beb6c0ba123336b5d05f2/verification/parts/p0/round3/intake/p1-intake/P1_INTAKE.md
[accept-files]: https://github.com/UyNewNas/goldbach-formalization/blob/28fd630ef7cc38eba86beb6c0ba123336b5d05f2/verification/parts/p0/round3/intake/p1-intake/P1_ACCEPT_FILES.json
[publication]: https://github.com/UyNewNas/goldbach-formalization/blob/28fd630ef7cc38eba86beb6c0ba123336b5d05f2/verification/parts/p0/round3/PUBLICATION_MANIFEST.json
[protected]: https://github.com/UyNewNas/goldbach-formalization/blob/28fd630ef7cc38eba86beb6c0ba123336b5d05f2/verification/parts/p0/round3/protected-sources.json
[fifth-scope]: https://github.com/UyNewNas/goldbach-formalization/blob/28fd630ef7cc38eba86beb6c0ba123336b5d05f2/verification/parts/p0/round3/intake/p1-intake/FIFTH_CANDIDATE_SCOPE.json
[live-fifth]: https://github.com/UyNewNas/goldbach-formalization/blob/28fd630ef7cc38eba86beb6c0ba123336b5d05f2/verification/parts/p0/round3/intake/p1-intake/LIVE_FIFTH_CANDIDATES.json
[geometry]: https://github.com/UyNewNas/goldbach-formalization/blob/28fd630ef7cc38eba86beb6c0ba123336b5d05f2/verification/parts/p0/round3/candidates/p1/HistoricalUpperFiveCellGeometry.lean.txt
[integral]: https://github.com/UyNewNas/goldbach-formalization/blob/28fd630ef7cc38eba86beb6c0ba123336b5d05f2/verification/parts/p0/round3/candidates/p1/ActualHistoricalFifthCellIntegral.lean.txt
[core-run]: https://github.com/UyNewNas/goldbach-formalization/actions/runs/38250288277
[core-job]: https://github.com/UyNewNas/goldbach-formalization/actions/runs/38250288277/job/114814517789
[ve-run]: https://github.com/UyNewNas/goldbach-formalization/actions/runs/38250288172
[artifacts]: https://api.github.com/repos/UyNewNas/goldbach-formalization/actions/runs/38250288277/artifacts
[workflow]: https://github.com/UyNewNas/goldbach-formalization/blob/28fd630ef7cc38eba86beb6c0ba123336b5d05f2/.github/workflows/lean.yml
[root-source]: https://github.com/UyNewNas/goldbach-formalization/blob/28fd630ef7cc38eba86beb6c0ba123336b5d05f2/ImbalancedChen.lean
