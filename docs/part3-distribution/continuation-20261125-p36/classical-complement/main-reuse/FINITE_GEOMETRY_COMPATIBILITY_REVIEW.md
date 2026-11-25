# FinitePrimeGeometryCore import diamond：独立源码审查

日期：2026-11-25。范围固定为 `a4f7fae932e6ac71c27791b3bf303ddfef285736` → `bc39fc4c2b821185443dda199ba199040d6c41a4`。只核对这次真实 import 兼容问题及其记录，没有重做 RootV 预检，没有编译或提交。

**结论：未发现本次结构修复改变原声明、假设或证明，亦未发现选定源码中的剩余显式 public 重名。六个 canonical owner 保持原文件 bytes，Core 复用其 imports，避免了同一全名由两份模块分别定义。该结论属于源码兼容审查；当前修复仍待真实重新编译和 kernel/完整声明验收。**

## 1. 原失败及修复性质

[tenth-all-rank-duplicate-declaration-failure.log](tenth-all-rank-duplicate-declaration-failure.log) 的 SHA-256 为 `c26c1f07432ca9b2fb10b11accc4f4f0dca845f29c50d0a87cf117dacb52a637`，623 bytes / 3 lines，与终点提交逐字相同。它记录 `Part3ActualCompactAllRankSupport` 导入时，`OrdinaryRosserFirstExitPolicy` 的 `ImbalancedChen.ordinaryRosserPrefixAdmissible` 已由 `FinitePrimeGeometryCore` 定义。这是实际 import environment 的重复定义失败，没有到达本模块定理证明或成功验收。

Core 的变化是移除六段重复抽取 section，改为 import 六个真实 owner；不是只通过调整 import 顺序掩盖冲突。AllRank 仅新增显式 Core import。FifthBudget 仅打开既有 `P2OriginalLowerSelectedCapConstructor.prefixCode` 名称；没有改声明正文，也没有新增依赖或假设。

## 2. 声明正文和 owner 原样保留

已独立核对 [FINITE_GEOMETRY_COMPATIBILITY.json](FINITE_GEOMETRY_COMPATIBILITY.json)（SHA-256 `2c2fe0192e7dfd770394b73bcc3436feddcf8d04ffa4b2c14c14054eb6708edb`）中全部 18 条记录：从旧 Core 和对应 owner 的实际声明起点取原始 bytes，检查完整正文边界、字节数、SHA 及相互相等；18/18 通过静态字节比对。六个 owner 整文件 SHA 与记录一致，而且旧提交、新提交和审查时工作树完全相同。

| Canonical owner | 复用声明数 | 递归项目闭包大小 | 闭包依赖 Core |
| --- | --- | --- | --- |
| `OrdinaryRosserFirstExitPolicy` | 2 | 24 | 否 |
| `FrozenRosserPolicy` | 3 | 26 | 否 |
| `PrimeHistoryLogCoordinates` | 5 | 32 | 否 |
| `FirstExitHistoricalLevels` | 3 | 37 | 否 |
| `ActualPrimeBoxMass` | 2 | 45 | 否 |
| `ActualPrimeBoxTestFunctions` | 3 | 48 | 否 |

旧 Core SHA 为 `becd322d719aa8ae9f0cc7b3bedbc19b87edd347bbc79788ce8f6ca7e5694d85`、Git blob 为 `fe7756f82e10c5ddf2f163535d35f0cb17d688dd`；新 Core SHA 为 `9f2f7e82b7bf19eaa326d10e1a04885c344f8bb39b259f76265b8a7b0dfd59cf`，均与兼容记录吻合。从 `OrdinaryUpperFiveAffineGates` section 标记直到文件末尾，旧/新 Core 整段 bytes 完全相同，因此剩余声明及其 namespace/section 上下文均未被编辑。

## 3. 闭包、重名与验收要求

按实际去注释/字符串后的 imports 重算全部 261 个选定模块：没有缺失项目 import，没有循环。261 个 sources 和 5 个 compatibility companions 共 266 个文件的 SHA 均匹配终点提交、manifest 和审查时工作树。manifest SHA 为 `26ca19a623efcb72064ac49e3fab02a15285de272601b62952dc779b60aa2206`，source guard 绑定正确。

对 261 份源码另作 namespace/section 感知的显式声明扫描（排除 private 声明），没有 scope 解析失衡：移出的 18 个全名各仅剩其唯一 canonical owner；Core 剩余 18 个显式 public 全名在选定集合内各只定义一次；整个选定集合也未检出其他显式 public 全名重复。`HistoricalPrefixCapData` 的唯一结构定义及其显式 namespace 成员仍在 Core。此扫描不代替 Lean elaboration 对生成声明、外部环境和实际加载对象的检查，不能据此提前保证运行时无任何其他冲突。

整个 `verification/` Git tree 在两个端点均为 `879002f0dc10ca87c6c6069e13bdd7b2352cdfd2`；runner SHA 均为 `895a8bc67d6c28e4db0ce6954344e20679cb581e3b861bafed469852d5ee5d30`。本次没有降低 fresh strict compile、bundled leanchecker、完整 owned/type/传递公理审计或实际 source/object/path 绑定要求。

## 4. 冻结与未赋予的信用

RootV 的两份准备 JSON 保持原 bytes 和 `a4f7fae932e6ac71c27791b3bf303ddfef285736` 基点：preflight SHA 仍为 `b09d17ee57e060d36982bcdf39e46c02d342efa0187c269fcfbb4086c3298519`，integration plan SHA 仍为 `f8549c52f2e8fd60147b92ccf932045079420264eae776636278ad262ca1704a`。没有把本次 Core 兼容改动写回旧预检，也没有把旧预检当作新基点验收。

本次仅新增此审查报告；没有修改数学、源码清单、runner 或原失败日志。后续仍须以修改后的精确 source/dependency hashes 重新构建相应对象，并对实际成功 archive 独立核证，不能沿用旧 Core 对象的历史成功状态给新文件计分。
