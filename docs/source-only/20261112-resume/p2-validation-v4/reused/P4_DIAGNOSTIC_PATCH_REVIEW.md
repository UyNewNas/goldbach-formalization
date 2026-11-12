# P4 FinitePiIntegral 失败诊断补丁独审

**静态复核通过。** 原失败头 `fb34e16802e8d0dffdd7d77b3ab442fc84ad55ed` 的 `verification/parts/p0/Round6Audit.lean` 与待用文件之间只有一处增加，位于第 75 行原比较和原抛错之间，共 41 行、2,519 字节。原完整声明相等、类型、公理检查和成功分支逐字节相同。候选未执行。运行 43108198136 的完整声明门仍失败，现有日志无法识别冲突名。 [原程序第 75 行](https://github.com/UyNewNas/goldbach-formalization/blob/fb34e16802e8d0dffdd7d77b3ab442fc84ad55ed/verification/parts/p0/Round6Audit.lean#L75)

| 实物 | 字节 | SHA-256 | 原始 Git blob |
| --- | ---: | --- | --- |
| 失败头源码 | 7531 | `394d26cd37a6fcd8611079ff1f8fa9aba1f757b59509ba9418cce7f45d17b100` | `60241d24546de4f62b709734bf44a89fb5543870` |
| 诊断候选 | 10050 | `46eedd90437fae00921f2a5a6a39abb5996125f45033b230c17d1403d16eec95` | `853f1a12de896ae0857e2b7e3b3f0900d31788bc` |

核对使用失败头的原始 Git 对象和候选文件，独立重算两份 SHA-256、blob 及文本字节差。锁定 Lean 版本为 `62eed1db4d67327ec8120be05f1a1b0847d74561`。

- `countName` 按 `Array Name` 用结构相等逐个计数。两清单的去重并集只用于枚举要比较的名称，两侧的重数都从原数组独立取得。因此两种方向和重复项差异都会保留。`Array.foldl`、`Array.contains`、`ModuleIdx.toNat`、以 `ModuleIdx` 读取数组、`getModuleIdxFor?`、`env.find?` 和 `ModuleData.extraConstNames` 均有对应版本定义。 [Array](https://github.com/leanprover/lean4/blob/62eed1db4d67327ec8120be05f1a1b0847d74561/src/Init/Data/Array/Basic.lean#L1080) · [ModuleIdx 和模块数据](https://github.com/leanprover/lean4/blob/62eed1db4d67327ec8120be05f1a1b0847d74561/src/Lean/Environment.lean#L86) · [归属查询](https://github.com/leanprover/lean4/blob/62eed1db4d67327ec8120be05f1a1b0847d74561/src/Lean/Environment.lean#L1195)
- `Json.arr` 接受 `Array Json`，`Json.mkObj` 接受键值列表，`ToJson` 提供数组及可选值实例。原审核程序也使用相同的 `map Name.toString`、JSON 压缩和 stdout flush。新增记录在原 throw 前刷新。结构比较保留精确 Name，但日志采用可读字符串。Lean 的文档说明含数值分量、匿名或含右书名号的名字可能无法通过字符串反向得到原始 Name。 [JSON 构造](https://github.com/leanprover/lean4/blob/62eed1db4d67327ec8120be05f1a1b0847d74561/src/Lean/Data/Json/Basic.lean#L185) · [JSON 编码](https://github.com/leanprover/lean4/blob/62eed1db4d67327ec8120be05f1a1b0847d74561/src/Lean/Data/Json/FromToJson/Basic.lean#L123) · [Name 显示](https://github.com/leanprover/lean4/blob/62eed1db4d67327ec8120be05f1a1b0847d74561/src/Init/Data/ToString/Name.lean#L114)
- `loaded_occurrences` 枚举所有已加载模块的主数据 `header.moduleData[*].constNames` 与 `.extraConstNames`。`canonical_owner` 来自真正的环境归属表。审计要求目标为 legacy 模块，此时其 IR 数据与主数据相同。对于其他采用新模块系统并带有独立 IR 的已加载模块，导入器可能从单独的 IR 数据向归属表插入名字。解释日志时应保留此范围，尤其在某个归属无法用已列出的主数据重现时。 [主数据和 IR 选择](https://github.com/leanprover/lean4/blob/62eed1db4d67327ec8120be05f1a1b0847d74561/src/Lean/Environment.lean#L2045) · [导入时登记所有者](https://github.com/leanprover/lean4/blob/62eed1db4d67327ec8120be05f1a1b0847d74561/src/Lean/Environment.lean#L2332)

本复核没有运行 Lean、构建、检查器或 CI。独立类型检查和该诊断在真实不匹配时的输出仍须由后续获准的运行提供。
