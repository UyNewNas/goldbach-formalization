# Part 3 小批交接：真实素数 BV 导入诊断

## 后续小批：首个直接供应者三门完成

在本交接记录的 185 个缺失导入对象之后，已单独恢复并验收
`ImbalancedChen.ChenQuotientSieveRemainders`。生产源码保持 SHA256
`caaca61f7e87eab1fe60b82b09d1f3438ebcace6b16f9ed7eac2d2411646664e`；严格
`trustLevel=0` 编译、同对象原装 `leanchecker` 重放、34 项全部所属声明审计和审计对象重放均通过。
完整编译器类型、公理列表、4,237 条实际 import 对象身份、原始日志及对象归档见
[supplier-chen-quotient](supplier-chen-quotient/README.md)。

这消除了两个直接导入中的项目供应者，不代表目标模块已经编译。另一个直接供应者
`MathlibNt.AnalyticNumberTheory.BombieriVinogradov.Bombieri1965Richert418Unconditional`
及其冻结 goldbach BV 闭包仍待恢复；`Part3PrimeAPDistribution` 的新增编译器确认定理数仍为 0。

## 验收结论

**状态：BLOCKED_MISSING_IMPORT_OBJECTS。本批新增编译器确认定理数为 0。**

本批从真实分支头 `f37f341412eb239f7e7e8937921ee8d01c9c2922` 继续，只处理 `ImbalancedChen.Part3PrimeAPDistribution` 的已有候选。该文件没有改动。原装 Lean 前端实际启动，但在第一个导入处失败；因此没有产生目标对象，没有进入目标声明 elaboration，也没有执行目标内核重放或传递公理审计。

本交接所在提交是独立的诊断检查点，不是该模块的证明验收。上一批 `Part3LongSlotNormalization` 两条定理的严格编译、生产对象重放和完整定义模块公理审计回执仍保存在 [长槽交接](../long-slot-normalization/HANDOFF.md)，本批未重跑或降级它们。当前高物理模数主线没有因此闭合。

## 固定版本与源码

| 对象 | 固定值 |
| --- | --- |
| 起点 / 源码提交 | `f37f341412eb239f7e7e8937921ee8d01c9c2922` |
| 起点 Git tree | `b6bcbedaf527e8894fd4d05a1df1d68463b47ac5` |
| 共同证明基线 | `1a80c1bcce67886f699d097fc37fd245cd3620bf` |
| Lean | `leanprover/lean4:v4.33.0-rc1` |
| 实际前端 Lean.githash | `62eed1db4d67327ec8120be05f1a1b0847d74561` |
| mathlib | `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1` |
| goldbach | `09b97db5764ade1246bfb77206baa1b124760958` |
| 手稿 | `ba6ec11d800eccc54406490631895e174de85766`，仍按 `docs/CURRENT_MANUSCRIPT_MAP.md` |
| 目标源码 Git blob | `2d761133b313302ab3a89ae906eb6944037a093d` |
| 目标源码 SHA256 | `55319b7e1150799a5bd2ed4bcc0ef3dd486de57409d9b859f678c068bcb8c7fc` |
| 目标 `.olean` | **不存在，不能提供对象哈希** |

原工作区缓存被环境清理后，本批按远端固定树逐 blob 恢复全部 348 个文件；没有把其他 Part 的较新源码混入本分支。目标依赖图涉及的 25 个本仓库源码全部与本分支匹配。11 个依赖包的 Git HEAD 与冻结 manifest 全部一致，相关依赖包源码逐 Git blob 核对无差异。这些检查确认源码版本；它们不等于现存缓存对象已经取得对应 producer/source/import 的验收身份。

## 实际执行与退出码

| 项目 | 实际结果 |
| --- | --- |
| 单模块严格前端编译 | **执行，退出码 1，3.326 秒；未超时** |
| `trustLevel=0` / 严格模式启动标志 | 日志中实际出现 |
| 生产源码、直接导入对象状态、工具及驱动前后比较 | 全部保持不变 |
| 目标生产对象 | 未生成 |
| 原装 `leanchecker` 目标重放 | **未执行：没有目标对象且导入闭包不完整** |
| 全定义模块传递公理审计，含 private/generated | **未执行：同一依赖阻塞** |
| 编译器确认定理类型 | **无** |
| 完整源码 / 依赖图归档 | 解码、成员清单和全部成员 SHA256 回读核对通过 |
| 依赖构建 / 全库构建 / CI 手动调度或重试 | 均未启动 |

实际执行的外层命令（退出码也是 `1`）：

```sh
python3 verification/parts/p3/prime-ap-distribution/diagnose_imports.py --config /workspace/scratch/e8f85e58ac36/round4/runtime-config.json --output-dir /workspace/scratch/e8f85e58ac36/round4/diagnostic
```

它调用的原装工具命令如下。完整环境和工具哈希保存在 [runtime-config.json](runtime-config.json)，逐次结果保存在 [strict-compile-receipt.json](strict-compile-receipt.json)。

```sh
/workspace/scratch/127408f63891/lean-runtime/lean-4.33.0-rc1-linux/bin/lake -d /workspace/scratch/127408f63891/lean-runtime/frontend-driver -f lakefile.lean script run compileOne /workspace/scratch/e8f85e58ac36/goldbach-formalization/ImbalancedChen/Part3PrimeAPDistribution.lean ImbalancedChen.Part3PrimeAPDistribution /workspace/scratch/e8f85e58ac36/round4/diagnostic-objects/ImbalancedChen/Part3PrimeAPDistribution.olean strict
```

此次复用现成的 P1 官方前端驱动及其串行调度，未修改驱动。驱动调用 `Lean.Elab.runFrontend`，`trustLevel := 0`，`warningAsError := true`；没有启用 cache metadata adapter。原装 `lean`、`lake`、`leanchecker` 及共享库哈希与前次记录相同。实际启动证明本地工具仍能通过现成驱动运行，不能将这次失败归为单纯的 `LEAN_NOT_ON_PATH`。

实际 Lean 诊断：[strict-compile.log](strict-compile.log)。

```text
FRONTEND_START module=ImbalancedChen.Part3PrimeAPDistribution trustLevel=0 strict=strict Lean.githash=62eed1db4d67327ec8120be05f1a1b0847d74561
/workspace/scratch/e8f85e58ac36/goldbach-formalization/ImbalancedChen/Part3PrimeAPDistribution.lean:1:0: error: object file '/workspace/scratch/127408f63891/goldbach-formalization/.lake/build/lib/lean/ImbalancedChen/ChenQuotientSieveRemainders.olean' of module ImbalancedChen.ChenQuotientSieveRemainders does not exist
```

这里只得到导入失败，尚无关于 13 个 theorem 证明体是否通过 elaboration 的编译器结论。原始日志是有缓冲的 stdout/stderr 合并输出，行的显示顺序原样保留。

## 最小后续依赖

源码级递归图共 6,472 个模块，含目标；这是静态图盘点，**不是成功加载后的 Lean 环境模块数**。

| 来源 | 静态图模块数 | 缺少 `.olean` |
| --- | ---: | ---: |
| 原装 Lean | 2,323 | 0 |
| mathlib | 3,580 | 0 |
| goldbach | 270 | 184 |
| 本仓库，含目标 | 25 | 2 |
| 其他包 | 274 | 0 |
| 合计，含目标 | 6,472 | 186 |

扣除目标自身，缺少 **185 个导入对象**。两个直接导入均缺失：

| 直接导入 | 源码 SHA256 | 对象 |
| --- | --- | --- |
| `ImbalancedChen.ChenQuotientSieveRemainders` | `caaca61f7e87eab1fe60b82b09d1f3438ebcace6b16f9ed7eac2d2411646664e` | 缺失 |
| `MathlibNt.AnalyticNumberTheory.BombieriVinogradov.Bombieri1965Richert418Unconditional` | `26de321b7b9ad1f3259c61461cd7259486c72a3404a9e32edabffd0cb9fb2f10` | 缺失 |

完整的 185 项名称、拓扑上第一批缺项以及全部路径见 [missing-imports.json](missing-imports.json)。对当前 11 个相关归档的只读搜索未找到上述两个直接导入的对象，见 [archive-search.json](archive-search.json)。P0 旧 core 日志存在 `ChenQuotientSieveRemainders` 的成功构建和重放记录，但现有归档没有该对象，不能拿日志替代编译所需文件。

接收 Part 0 的最小请求是：

1. 恢复或安排生成固定 `goldbach@09b97db5764ade1246bfb77206baa1b124760958` 的上述 BV producer 导入闭包；清单里 184 个 goldbach 缺项均保持原源码。随对象提供工具链、生产源码和实际导入对象身份。
2. 恢复同源 `ChenQuotientSieveRemainders.olean`，或只构建该单个项目依赖。不能混入新 baseline 的定义对象。
3. 闭包完整且来源绑定后，Part 3 再对未改动目标依次做严格编译、原装生产对象重放、全部 defining-module 声明的传递公理审计。最后一门应与序列化模块声明库存对齐，包含 private/generated，并绑定三门相同的生产源码、目标对象及实际导入对象。

本批没有自动启动 184 个 goldbach 模块的重建；缺项清单也没有被改写成任何解析定理的假设。普通 object presence 盘点没有冒充完整 cache provenance 或传递公理审计。

## 已核对的准确供应者差异

[SOURCE_REVIEW.md](SOURCE_REVIEW.md) 逐条核对 13 个定理的现有证明和 pinned API；[SOURCE_TYPES.md](SOURCE_TYPES.md) 保存全部 13 个 theorem 和 2 个 def 的完整**源码声明头**。二者都明确不是编译器确认类型。

Pinned `AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418.standardBombieriVinogradov` 在源码中有正常证明体，直接提供 `StandardBombieriVinogradov`，不留待供 SW 参数。它提供所有前缀和所有本原剩余类的最大误差之和；生产候选据此适配真实素数共同区间、逐模数变化的互素余数和一有界实模数权重。两端点使用同一 BV 阈值，付出因子 2。

量词顺序保持 `∀ A>0, ∃ B≥0, ∃ C>0, ∀ᶠ N, ∀ Q,S,L,U,a,w, ...`。阈值先于全部支撑、区间、移动余数和系数，不是逐参数阈值。中心准确为 `trueLogarithmicIntegral x = 2/log 2 + ∫₂ˣ dt/log t`；共同区间作差时固定常数消去。

其完整物理模数仍受 `Q ≤ floor(N^(1/2)/log(N)^B)` 限制，素数变量加性相位为零，权重是外部模数上的 `w : ℕ → ℝ` 且 `|w d|≤1`。这不提供 `theta_* = 599/1000` 的高物理模数、prime-product source、packet 内部系数、rough 槽或非零共同相位，也不提供 Brun/Mellin 转移成本及实际参数长度许可。旧弱 Pan/Selberg 路线没有被当作当前主线替身。

对于实际 quotient 下源，完整模数 cap、合法系数类、源恒等式、中心修正和因子分解许可仍须在实例化时核对；本批不能声称实际上／下误差供应者已闭合。这些数学输入与本次对象缺失是两类独立的未闭合事项。

## 接收与文件范围

**接收 Part：Part 0 记录依赖阻塞及安排同源 BV 缓存；Part 3 在闭包恢复后继续局部三门。** Part 1 无需先交齐实际策略来解除本次构建阻塞。Part 1 的完整 cap、系数界、源恒等式及分解许可用于后续实际实例化。

本批只新增本目录的诊断／审查／回执文件，并在 `docs/part3-distribution/README.md` 添加入口。所有生产 `.lean`、工具链和依赖配置、手稿地图、旧完整验证器及 workflow 均保持原 Git blob。没有新增 `sorry`、公理、`native_decide` 或待证误差前提；没有新增仅含目标 Prop 的 Lean 模块。

本目录的 [receipt.json](receipt.json) 是机器可读汇总，[evidence-manifest.json](evidence-manifest.json) 绑定本批文件哈希。完整静态图、源码恢复证据及驱动原文收在 `inventory-evidence.tar.xz.b64`；[归档清单](inventory-evidence-manifest.json) 给出解码后的哈希、每个成员哈希和实际回读核对结果。解码示例：

```sh
base64 --decode inventory-evidence.tar.xz.b64 > /tmp/p3-prime-inventory-evidence.tar.xz
tar -tJf /tmp/p3-prime-inventory-evidence.tar.xz
```

这些文件没有提供本次未生成的目标或 BV 依赖对象。
