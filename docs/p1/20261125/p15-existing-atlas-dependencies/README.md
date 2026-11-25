# 既有 Atlas 依赖：已验收源码的原样复用

本目录记录 9 个 canonical 源文件对既有已验收 postimage 的原样采用。状态为 **既有接受证据复用，非新 Lean 接受**。本次没有重写证明，没有调用 Lean、Lake、kernel checker 或云编译，也没有复制或修改任何缓存。

基准提交为 `d20acdf13882e17d97833064f5e7c54f3192b03c`。9 个 owner 与该提交阶段 1 的 `p15-singleton-proper-power/SOURCE_CLOSURE.json` 所列 316 项源码交集为空；原有阶段 1 源码与执行脚本均未修改。

## 采用的来源与范围

全部新 canonical 字节取自固定提交 `a392cd8efcf4f0b4adf3d12f2d8db41370309ed3` 的以下目录：

`docs/verification/20261123-blue-compilation/reindex-isolated/postimages/ImbalancedChen/`

| 依赖顺序 | Owner | 修复范围 |
|---:|---|---|
| 1 | `P5OriginalHBMediumChartReserves` | 原有 rpow 证明中的数值 cast 归一化 |
| 2 | `P5SmoothChartPhysicalHBBranch` | 原有 `rawProduct` cast 与已化简分支的反身性 |
| 3 | `P5ActualMultiGroupHBChartScale` | 原有证明兼容修复及独立记录的 grouped-field 语法修复 |
| 4 | `P5ActualHBChartEventualClosure` | 原有乘法消去、List、cast 与 tactic 兼容修复 |
| 5 | `P5OriginalChartRoughCutoff` | 使用现有正乘法消去 API |
| 6 | `P5ExactOriginalSmoothDyadicPartition` | 展开既有 `R` 及 List 长度零 API 修复 |
| 7 | `P5ActualLabelledPrimeSmoothCharts` | 原有 cast 修复及既有 dyadic `R` 的局部解析修复 |
| 8 | `Part3OriginalProperPowerChartCount` | 原有素数下界、平方、乘积括号与 cast 的证明修复 |
| 9 | `Part3ActualOriginalProperPowerChartBridge` | 原有有限积、List/get/cast 与 namespace API 修复 |

`ADOPTION_MANIFEST.json` 逐项保存 canonical 路径、完整 before/after SHA256 与 Git blob、旧源快照路径、accepted Git commit/path、imports、修复类别、normal/kernel/public-owner 证据以及新保存的 donor 对象与 trace 哈希。`preimages/` 保存 9 份基准源码原字节。历史 postimage 与历史证据文件均保持原样。

这 9 项的直接 import 列表完全不变。独立重放旧 `API_IDENTITY.json` 记录的限定修改块可以逐字节重建全部 9 个 accepted postimage。最大相关 Bridge 项目源码闭包有 68 项，修改前差异恰为这 9 项；采用后 68 项源码 SHA 均与历史 accepted selection 一致。

## 两项公开合同例外

其他 7 项只改既有证明体。以下两项保留原独立源码审查中的明确例外，不能笼统声称所有声明 header 字节或旧、新 elaborated type 相同。

### `P5ActualMultiGroupHBChartScale`

将 `R z y : ℝ` 与 `j n : ℕ` 分别写为 `(R z y : ℝ)` 与 `(j n : ℕ)`。这恢复原消费者分别使用的五个 intended fields：`R`、`z`、`y` 为实数，`j`、`n` 为自然数。原有 `positive`、`rough_nonneg`、`hb_nonneg`、`hb_cube`、`lower_support`、`upper_support`、`order`、`active` 八项约束保留，假设和数值常量不变。

原定义没有成功 elaboration。因此本记录不声称旧、新 elaborated type 已证明等价；这是既有消费者及原稿含义支持、并已在 isolated 环境接受的语法修复。

### `P5ActualLabelledPrimeSmoothCharts`

在既有 noncomputable section 中加入 `local notation "R" => ExactOriginalSmoothDyadicPartition.R`。六处原有 bare-`R` 用法均是 dyadic chart index，指向已有定义 `R (j : ℕ) : ℝ := (2 : ℝ)^j`，并与同一 supplier 的 `R_pos`、`tupleProfile`、`psi_left`、`psi_right` 一致。

此修复消除与 PNT 误差函数 `_root_.R (x : ℝ) := Psi x - x` 的解析歧义。公共声明 header tokens、假设和常量保留；局部 notation 不引入新环境声明或导出的 alias。旧版没有可比较的已接受、无歧义 elaborated type，本记录不作此类等价声明。

## 既有接受与当前对象定位

历史接受范围是 isolated Reindex 的 70 项项目源码与 456 项 native 源码：完整 target normal build、1742 项公开声明的类型／公理审计、canonical public-owner 覆盖，以及 19 个指定 owner 的 native named kernel replay。这 9 项均在 named kernel 列表中；各自对象 SHA、checker command、日志 SHA 与公开 owner 数均保存在 manifest。

该 kernel replay 使用各 named module 的原 imported environment；它不是 `--fresh` 全依赖重放，也不是外部独立验证器。canonical owner 覆盖比较的是已接受 postimage 环境的两种枚举，不是失败旧源与修复后类型的等价比较。

`P1_REINDEX_CACHE_OBSERVATION.json` 原样保存 root 的只读查询 `job_cd56a0b4f9bc4b4e98effb99ce592a24`。查询 root 为 `/workspace/blue-reindex-build`，针对 58 项缺对象列表定位到了 10 项对象：上述 9 项 accepted source 和 `.olean` SHA 全部匹配旧接受 pin；另一个 `P5SmoothChartHBDyadicPartition` 原样源码及对象也被定位。7 个 receipt／guard pin 与 3 个 isolated project configuration pin 同样匹配。

`P5SmoothChartHBDyadicPartition` 不在本次 9 文件修改范围中。它有旧 normal/public-owner 审计记录，但没有列入旧 kernel19 的独立目标；不得由本次定位追加该项 named-kernel 接受。

旧 isolated `lakefile.toml` 为 461 bytes；当前 P1 receiver 的配置边界仍需由后续缓存复用流程明确处理。本次只采用源码，不转移 `.olean`/`.trace`，不宣称 receiver 的完整 import 或部署验收已经完成。

## 只读核验

在仓库根目录执行：

```bash
python docs/p1/20261125/p15-existing-atlas-dependencies/verify_reuse.py
```

该脚本只读本地 Git 对象、源码、manifest 与已保存的查询结果。它检查固定 Git 来源、9 份 preimage、9 份原样 postimage、imports、旧限定修复块、阶段 1 的 316 项源码不变、相关 68 项源码闭包、旧 normal/public-owner/kernel receipt 与保存的对象匹配。脚本不联网、不 fetch、不写源码或缓存、不运行 Lean。

旧 phase2 源清单仍记录采用前的 9 个 SHA；相关 metadata 更新由对应 owner 单独完成。本次未修改 phase2、rough、trim 的文档、清单或执行脚本。额外 45 项的有限范围核查没有找到精确 owner 接受或失败 receipt；这不构成全局从未编译的断言，也不授权批量重编。
