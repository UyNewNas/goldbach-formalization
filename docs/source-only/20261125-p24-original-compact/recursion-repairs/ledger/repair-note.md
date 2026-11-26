# PriorityForestLedger：安全递归修复的隔离验证

## 结果与适用范围

最终候选 `frozen-candidate/P2OriginalPriorityForestLedger.lean` 共 35,301 字节，SHA256 为 `11e2a50288146a94cbb6351fd6f5b279469c6cce1d6af437569260d54880cc0c`。

P2 隔离任务 `4164a39fc61e485ebabec90f4761301a` 在冻结源 pin `6e616f4e0372555f7a78bcdba3e198d0e277eec8` 的原 lower 环境上完成编译、独立 leanchecker 重放和未经削弱的完整 owned 审计。三个阶段分别用时 19.704200、8.622749、7.814142 秒，均 exit 0。全部 201 个 owned 声明完整等量枚举；所有声明均 safe、nonpartial、nonaxiom，传递公理仅属于原允许的三项，完整类型文本共 335,338 UTF-8 字节。完整原始日志与收据见 `attempt-002/`。

这是隔离候选证据。canonical 源码、编译记录、原对象、运行时和 native 输入均未改变；尚未由本诊断取得新 source pin 的 canonical 编译、321 或完整 324 验收 credit。后续仍须以统一候选集运行原门控。

## 定义和行为

五处具名递归已替换为显式可计算组合：

- `treeEntries` 使用通用 `treeFold`，叶保留原 cell/enclose/serial，分支仍按左树、右树顺序追加。
- `eraseTree` 使用同一折叠，叶仍为 `.leaf`，分支仍使用原 `originalAxis` 和 `originalMidpoint`，左右次序不变。
- `entries` 与 `eraseForest` 沿完整索引列表 `cs` 使用 `List.rec`，每步仅解构相应 `SourceForest.cons`，保留全部森林条目和原顺序。
- `seedForest` 使用 `List.rec`；尾森林仍从 `advance enclose c s` 开始，当前叶仍使用 `issueSerial enclose c s`，最后 serial 仍来自尾结果。

所有 32 个原定理头逐字保持。原 imports、数值、guards、目标、资源选项和原 `noncomputable section` 字节保持；没有新建 noncomputable workaround。七处实际编译错误只通过已证明的叶/分支等式、保留尾函数头的 `change`，或归纳假设正规化解决。具体可逆替换列于 `attempt-002/source-patches.json` 和 `proof-patches.json`。

## 通用折叠及充分燃料

`treeFoldFuel` 采用直接 `Nat.rec` 与单层 `SourceTree` 模式匹配。`treeFold` 的内部燃料是三个原整数坐标宽度的非负部分之和再加一：

`(upper 0 - lower 0).toNat + (upper 1 - lower 1).toNat + (upper 2 - lower 2).toNat + 1`。

已有的 `originalMidpoint_interior c width` 只使用原 split 构造子的 width 证明。它保证选中轴的两个子宽度严格缩小；其他轴不变。因此每个子树的预算都严格小于父预算，无须增加坐标正性、有序盒或其他新前提。

私有稳定定理量化任意两个充分燃料，再证明公开 `treeFold_leaf` 和 `treeFold_split`。这保证最终 `treeFold` 对合法 `SourceTree` 不采用 fuel-zero fallback，并保持原构造递推。预算可能比实际深度大；本次记录只证明充分性及实际编译/审计结果，不据此宣称历史有限计算的性能已解决。

独立 `TreeFoldCandidate` 任务 `e046315a0a574746859728913b59e07b` 已分别通过编译、独立重放和完整 owned 审计，19 个 owned 声明全部合格。该原型中 4,422 字节的通用 helper 段被逐字纳入最终 Ledger 候选，SHA256 为 `57cf46d9212b5ae9e290dee15d61d5959580040b5cd050df30b3115ac52dd0e7`。原型额外 import 没有进入生产候选。

## 保留的失败和传输记录

首个通用原型尝试使用原自动 `sizeOf` 实例作为运行时燃料。任务 `fdf72889824f4a5695f42bdd24cecff2` 编译失败，唯一错误是缺少 `SourceTree._sizeOf_inst` 的 LCNF signature。该失败未用 noncomputable、unsafe 或旧递归实现绕过；随后改用上述原几何量并证明充分性。

Ledger 首轮 `5b38b1a6746f48f8a2cf0e5dc7ea9fcb` 保留原全部证明体，实际失败暴露七处展开后归纳假设的表示不匹配。最终候选仅修复这些证明位置。两次失败的源码、命令、日志和收据均完整保留。

Ledger 第二轮首次提交命令为 67,493 字节，API 以 65,536 字节请求上限拒绝，未创建任务。拒绝记录及原命令保留。随后只把同一 JSON 源码负载无损 gzip/base64 包装，命令变为 25,614 字节；候选 SHA 和所有 gate/assertions 均不变，再提交成功任务。此传输变化没有改变 Lean 源码或资源范围。

## 后续整合边界

最终候选没有导入隔离原型。它按原模块路径取代 Ledger 时，会提供公开 `treeFoldFuel/treeFold/treeFold_leaf/treeFold_split`，以及 `treeEntries_leaf/split`、`eraseTree_leaf/split`。下游隔离测试使用旧 canonical Ledger 时，只能证明其对应 lower 绑定；统一新 source pin 的原门控仍须确认全部新 lower 组合。

`publication-manifest.json` 逐文件绑定本次全部源、成功/失败日志、原模板、wrapper、可逆 patch 和传输拒绝证据。没有发布 tree、commit 或 ref 操作。
