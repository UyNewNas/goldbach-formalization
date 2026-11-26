# cell00 五个 original-archive consumer：冻结的待收据驱动

**状态：SOURCE_ONLY / 尚未执行 / 无新增形式化信用。**

本目录冻结下一次增量验证的源图、实际依赖选择、只读检查和驱动变更。驱动为上层目录的 `run_cell00_five_consumers_cloud.py`。旧 `run_cell00_consumers_cloud.py` 保持 SHA256 `4678b1b316d2741a5a0e80a47969ed42addbfc5ed067b6a27ecf4302f43db5a0`，没有修改或执行。五份选定 Lean 源码也没有修改。

## 当前唯一尚未具备的执行输入

Field attempt003 的**聚合成功 RESULT 及完整证据**尚未交付本包。`SOURCE_AND_RECEIPT_SELECTION.json` 的 Field 收据 SHA 为 `null`，`dependency_receipt_selection_complete` 为 `false`；驱动的 `FIELD_RESULT_SHA` 为 `None`。`main` 的首个检查立即拒绝这种状态，发生在检查远程目录、创建输出目录、调用 Git、修改 checkout 或执行任何编译命令之前。静态检查实际调用了这一拒绝分支，未执行 Lean、leanchecker 或远程任务。

已知 Field publication 是 `2ce35f759db6fdc18373b2842f655d9569fd4f48`，严格分块驱动 SHA256 是 `3b7740243e09c49d8ebfc0233a5f1a666a865132364d90a075b4980cc965176b`。单个分块的成功或运行中状态不能代替聚合成功收据。

收到并检查真实聚合成功收据后，应先保留本版前像，再更新实际 Field SHA、selection 完整标记及其 SHA 绑定，复核变更并重新冻结。未来执行者还必须把新驱动字节绑定到其精确 publication 的 Git blob。此 README 不授权绕过上述任何检查。

## 精确的新 owner 范围

编译顺序固定如下；所有公开名字来自实际冻结源码，最终 owned 数必须以完整导入环境及序列化模块审计为准。

| 顺序 | owner（省略 `ImbalancedChen.`） | 公开源码声明 | 本次作用 |
| --- | --- | ---: | --- |
| 1 | `P2Saving16Cell00Decoded` | 3 | 合成原 AST 身份与原 typed decoder 的成功结果 |
| 2 | `P2Saving16Cell00OriginalParse` | 3 | 将原字符串解析、原 decoder 与 `archive (0 : Fin 14)` 连接 |
| 3 | `P2Saving16Cell00OriginalFloors` | 10 | 原 archive 等于已接受 typed payload，并传递逐项 stored floors |
| 4 | `P2Saving16Cell00OriginalArithmetic` | 2 | 传递八个 simplex 的原 guard，并证明原 `cellFloorNumerator 0` 的值 |
| 5 | `P2Saving16Cell00OriginalSourceFacts` | 2 | 传递原 dependent Fin 上的 header 与 facet index guards |

源图共 **45 个项目模块**，初始隔离对象根恰好含 **40 个已接受依赖对象**。五个新 owner 在初始根中必须不存在。每个 owner 仅在其实际依赖全部接受后才执行；结束时精确检查 45 个对象。

前三份源码沿用 `c91601b4…`、`9bd6429b…`、`a74eb2b7…` 的既有 consumer；后两份源码沿用已冻结桥接文件 `86931583…`、`979cd17b…`。完整 SHA、路径、直接 imports、公开声明及每个目标的传递依赖清单均位于 `SOURCE_AND_RECEIPT_SELECTION.json`。

## 依赖收据与既有工作复用

| 分支 | 选择的实际 RESULT SHA256 | 当前状态 |
| --- | --- | --- |
| Field attempt003 | **待实际聚合成功收据** | 硬性阻塞 |
| Remaining arithmetic / AllRows | `1e48fc2e2a45b2e4247ab08597586dae6c8cac3cd9a05788e465b5175d262f7c` | 已接受，完整实际收据已读 |
| TypedSourceFacts | `498a435cb515686340b095fc9545cf6130cfad3b26390b61b03c541ee9e6dc8f` | 已接受，完整导出源码、对象、三日志、owned 清单和快照已核实 |
| 原 Row00 | `7094b47bfe97aaa8236cda1309e805440a3b6a1b48b5d4083fa6ba75cd2e8265` | 原 owner 字典保持；复用 AllRows 已有补充完整上下文验证 |
| Field 原三 owner | `86afeed917a3361c5457db1b7b3f4546d2e513531288adfab3d3a196ad38eac1` | 原 ecfc 来源保持；仅复用 attempt003 的补充上下文验证 |

Field 依赖必须恰好选取原三 owner 与十一新分块。原三 owner 的 publication 必须仍是 `ecfc75049ab7380048fa0c9992e14b787bc908de`；字典、source origin、三阶段命令和日志、完整 owned 声明均按原收据核验。原聚合失败的事实保持，失败 FieldDecode 对象不允许替代成功分块。Row00 原字典同样不改为后续 publication。

已经接受的数学 owner 不进行 normal、replay 或 audit 重跑。本次只读取既有收据、源副本、对象、阶段日志和审计记录，并把相同对象复制到一个新的隔离根。Field 的三份补充 replay/full-owned 记录和 AllRows 的 Row00 补充记录只读复用，必须证明它们保留原 owner 身份且没有 normal 重编。

对 FieldSimp，普通完整 owned 模板必须精确附加已冻结的 `ff82f03c…` appendix。驱动重新读取实际日志中的 private scoped simp marker，核对 296 个原 private 用户名、唯一实际 private 名称、helper owner 的完整声明清单，并核对保存的 interface JSON。此检查不执行新的 Lean 审计。

## 完整编译上下文

完整外部快照复用已接受 AllRows 运行的 `COMPLETE_EXTERNAL_BEFORE.json`，SHA256：

`b94ab99b39a831a616d626c55c4b89c0a921d15c95319de19063d375bc982728`

它包含 **5312 个外部对象和 10624 个 `.private` / `.server` companions**。驱动逐项比较唯一路径提供者、companions 清单、文件大小及 SHA；Field、AllRows、TypedSourceFacts 三支实际收据必须冻结同一组当前对象。所有新 gate 前后均检查 publication、Mathlib pin、路径提供者和全部冻结哈希，不能把后捕获的当前哈希冒称旧运行的历史哈希。

旧 OriginalJson 的实际完整 import 清单是 **2872 个外部模块**，为该完整快照的子集。它按已钉住日志中的 2872 模块与覆盖关系核验。其余本包已实读的 accepted owner 审计包含 5312 个外部模块；五个新 consumer 也要求完整的 5312 模块清单。

使用同一已接受 Lean / leanchecker 二进制及 Mathlib commit `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`。新 gate 使用 `-t0 -j1 -M11264 -DwarningAsError=true -DmaxRecDepth=1000000 -DmaxHeartbeats=80000000`。每个新 owner 依次执行 normal、独立 `leanchecker --verbose`、完整 owned 审计；每阶段墙钟上限 600 秒。完整审计包括 private/generated 声明，拒绝 unsafe、partial、axiom 声明以及超出 `propext`、`Classical.choice`、`Quot.sound` 的依赖公理。每份新日志、对象和 companions、owned JSON、inventory JSON 均加入冻结记录。

## 将来的接受范围

只有五个新 owner 的全部 gate 真正通过，才能接受以下 **cell00 实例**：原解析和 decode 成功、原 archive 的 payload 身份、逐项 stored floors、原 dependent Fin 上八个 simplex 的完整 guard、

`cellFloorNumerator (0 : Fin 14) = 13236428172062120`

以及原 header 和 facet index guards。`cellFloorNumerator` 使用原定义，保持八个 Jensen 值各自 Q96 下取整后求和；不另造归一化结论。算术/几何 Jensen 绑定的状态字段限定为 `original_cell00_geometric_jensen_binding_proved`。

完整 P2.5、十四 cell 聚合、原 source-cell 成员关系、所有 96 个顶点不等式、正法向平衡、facet incidence、pulling ownership 都不由这五份源码建立。其余十三个原 cell 的既有源码与任务继续复用，当前没有在此重做。原 1106 稿的因子 4、体积 `/8!`、mean gap `/9`、weighted means `/10`、两个 residual 加八个坐标因子、buffered cap 及有序九顶点身份均由已接受算术分支保持；本次桥接不重新计算这些内容。

## 本地只读验证

`STATIC_CHECKS.json` 记录了 45 个实际源码的哈希、imports 和公开声明检查，以及 **17 个实际已接受 owner** 的完整 owned/serialized/environment 清单对照。它还检查这些实际日志使用的外部模块均被完整快照覆盖，并核对严格阶段命令。

`TYPED_SOURCE_FACTS_DEPENDENCY_CHECK.json` 单独记录 TypedSourceFacts 实际 6 owned 声明与导出证据检查。`ADAPTATION_FROM_4678.patch` 是从未改动旧驱动到新驱动的完整文本差异。`FILES.json` 钉住本冻结包及新驱动；本地 Python 解析和收据读取不产生 Lean 证明信用。

## 独立审查修正记录

`p25_cell00_finite_guards` 在冻结版 `320b30e6…` 中确认一处 Python 路径类型错误：supplemental reuse 记录的 `stage.log` 是 JSON 字符串，但 `read_audit` 接口要求具有 `read_text()` 的 `Path`。本版只将该处调用改成 `read_audit(Path(...), module)`；运行逻辑只发生这一处、六字节的增量修改。

`review-fixes/` 保留该冻结版完整 runner 前像、原冻结元数据压缩前像和单行差异。修正后的原调用表达式已使用 AllRows 实际 Row00 supplemental AUDIT 日志执行 Python 数据读取核对，得到与原收据完全一致的 21 owned、inventory 及项目闭包；旧调用的 `AttributeError` 也已实际复现。这只检查路径接口及既有证据读取，不执行 Lean 或重复证明。Field 成功收据的空值和首句硬性阻塞均未改变。
