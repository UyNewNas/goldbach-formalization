# P0 只读复核：P3 LongSlotNormalization

**结论：固定提交 `f37f341412eb239f7e7e8937921ee8d01c9c2922` 的三门回执可复用，2 个所属声明的完整类型已确认，无需重复执行生产编译或重放。**

本复核没有运行 Lean、Lake、CI 或归档内的验证脚本；只读取固定 Git 源码、归档成员、原始记录及对象字节。
机器回执为 `P3_RECEIPT_REUSE.json`，复核程序为 `check_receipt_reuse.py`。

## 身份与逐项核对

| 项目 | 固定值 / 核对结果 |
| --- | --- |
| 源码 SHA256 | `ca4e4d237bb4a5d21f72af3223001621902d6763d0b7ef1f423f532fd94f69fc` |
| 源码 Git blob | `3e9aa6a43744d43e38d705d754963dba53e657e6` |
| 生产对象 SHA256 | `a74f51987d4e5ea037a2a9f9a5d9a74251ba7f697d4bede12f9252b9ef36a7e7` |
| 严格编译 | 原始 exit 0，9.477 秒；trustLevel=0、warningAsError=true |
| 原装内核重放 | 原始 exit 0，2.785 秒；有确切目标 `replaying` 行 |
| 完整所属声明审计 | 原始 exit 0，15.226 秒；2 个 theorem |
| base64 文件 SHA256 | `c24b2135131e418ea7648ccf3ba8e4e9e8f33b62155541040f037bf3e67a16a0` |
| xz 归档 SHA256 | `eb8178c7abd4848ca24e3da906c76e549d7babf800ba13e8c44d182aa9eadbe3` |
| 归档 | 2,167,916 字节；35 个 regular-file 成员，解压数据共 72,946,148 字节；全部成员尺寸及 SHA256 一致 |

固定源码与归档源码相同。旧 `7d70a2545fd819706e473eb41e4d430ad19119d8` 的本地 Git commit 未在本次浅取回范围内，
故按任务许可，使用固定归档内该提交的完整 remote tree：旧模块 blob 与当前源码重新计算的 Git blob 完全相等。
未凭 source-unchanged 布尔值单独下结论，也没有为此补构建。

导入的 `Part3LongSlotDistribution.lean` 与 P0 固定 `80aca6710c83b5160f4c5fdd05d180e507990e95`
的实际 Git 源逐字相同：SHA256 `67ccc48e6a4befadfd4b5639e2cdb4bd43e443b8f4eaf3086fe5a6c5fbd0023e`，
对象 `fd8cdcf5ac894e5b904f8bdc0e80506b16c23bb17bc1a568ea4a3a5b50b61816`。

## 导入及三门身份

严格编译与重放的完整导入库存完全相同：4,957 个模块、29,642 个源码/对象部件文件。
每个模块的 source、主 `.olean` 及实际存在的 server/private/ir/ir.sig 部件都在哈希库存中；路径集合与哈希集合双向相等。
4957 份 source hash 与 source-closure manifest 逐一相符。

成功 audit 仅额外加入目标源和目标对象，变为 4,958 个模块、29,644 个文件；
共有 4957 个模块的布局和全部文件哈希与生产门完全相同。
完整原始 audit 中由 Lean 实际导入环境及 `Lean.findOLean` 输出的 4958 模块及路径，与预期库存双向完全相符。

逐项核对了三个 selected gate 与归档原始 receipt 完全相同、原始日志首记录一致、日志 SHA256 一致、
生产源码前后相同、生产编译对象等于 replay/audit 前后对象、无 verification_failure_reasons。
归档 runner 确实重新计算完整 after capture 并强制比较；相等的 after 数组没有再次重复存储，
原始记录保留空变化集合及全量相等结果。本复核没有虚构另一份 after 文件。

## 类型与安全审计

两个声明的原始 audit JSON、独立 compiler-declarations.json 和 COMPILER_TYPES.md 完全相符；
可读及 `pp.all` 类型均无 `⋯` 或 `...`。
审计实际枚举 defining module，且与序列化 `ModuleData.constNames` 集合双向相等：
`is_module=false`、`import_all=true`、`has_data=true`、constant count 2、extra codegen names 0。
逐项 `isUnsafe`、`isAxiom` 及传递公理检查覆盖全部 2 声明，实际公理只含标准三项。

确认类型保持：先固定 `theta < 1`、`epsilon > 0`（对数版本另固定自然数 K），再有统一 eventual N 阈值，
然后对全部 M、D、L、U、a、alpha、rho 量化。
实际输入仍为 `M*D ≤ N^theta` 及完整实际支撑上的系数范数 ≤ 1；
结论分别为 `epsilon*N/log(N)^K` 和 `epsilon*singularNormalization N`。
未增添 `theta ≥ 0`、区间次序或待证分布前提。

## 首诊断和当前对象

生产源码首次严格编译通过，没有证明修复。
audit 的两个旧失败是审计入口格式问题，按原始日志保留：

1. exit 1，4.522 秒：`cannot use import all without module`，审计 1:7。
2. exit 1，9.689 秒：`cannot import non-module ImbalancedChen.Part3LongSlotNormalization from module`，审计 1:0。

随后 legacy audit 通过，生产源码和对象未变。
旧生产输出绝对路径现已不存在；固定归档内的目标 `.olean` 确实存在并匹配全部三门哈希。
本复核将该既有对象恢复到 `verified-archived-object/ImbalancedChen/Part3LongSlotNormalization.olean`，没有重新生成证明对象。

## 接收边界

P0 可按固定 SHA 分批接收此 1 模块、2 声明。P3、P4-B 和 P5 可复用其归一化接口。
仍需实际政策证明 `MD ≤ N^theta`、`theta < 1`，以及 rough/prime 长槽、长槽相位、Brun/Mellin 成本、
restricted medium 和 two-long 的供应。此回执不是全库构建、完整 Part 3 分布或全部导入的新内核重放。
