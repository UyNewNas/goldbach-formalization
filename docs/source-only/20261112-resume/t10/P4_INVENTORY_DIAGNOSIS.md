# P4 FinitePiIntegral 声明清单失败的独立诊断

**现有记录能确定失败的比较，不能确定冲突的声明名或本次差异的成因。** 运行 `43108198136` 在头 `fb34e16802e8d0dffdd7d77b3ab442fc84ad55ed` 上完成 146 模块编译和 kernel 重放。生成的 CandidateAudit 在 FinitePiIntegral 比较失败前只写出 68 个其他模块的序列化记录。它在打印目标模块的清单之前抛错，当时全审计目标的环境名称计数为 3,124。该 ZIP 只有对象哈希快照，未保存相应 .olean 文件。实际日志 SHA-256 为 `e9b71a7c3a10433b067aa2f0b999ba930757a786e401aec837b700db253673de`，被审 FinitePiIntegral 源 SHA-256 为 `22c7e16d66361c4aec2913237c8b8866db59575d36c50416805094e351f5c54c`。此证据不足以判定项目审计工具或 Lean 导入器有缺陷。 [失败运行](https://github.com/UyNewNas/goldbach-formalization/actions/runs/43108198136)

## 两种清单的身份

失败头和 `356c3782e9428098a2fcbfb18c689bef264d84fa` 共享同一份 Round6Audit，Git blob `60241d24546de4f62b709734bf44a89fb5543870`、SHA-256 `394d26cd37a6fcd8611079ff1f8fa9aba1f757b59509ba9418cce7f45d17b100`。失败头的 candidate 生成器是 blob `e24c62bbc821b9a263f83eb2b971b66436672174`、SHA-256 `6624ff00e39ddd52672c6402903c2040520d1ed78e265e7f64afcde8003d11f3`。它换入 146 个模块的 import 与目标数组并去除 finalBridge 专用输出，保留了失败的原始比较。 [Round6 源码](https://github.com/UyNewNas/goldbach-formalization/blob/fb34e16802e8d0dffdd7d77b3ab442fc84ad55ed/verification/parts/p0/Round6Audit.lean#L52) · [P4 生成器](https://github.com/UyNewNas/goldbach-formalization/blob/fb34e16802e8d0dffdd7d77b3ab442fc84ad55ed/verification/parts/p0/prepare_candidate_validation.py)

在锁定 Lean `62eed1db4d67327ec8120be05f1a1b0847d74561` 的 Environment.lean 中，模块的 constNames 由其实际序列化 ConstantInfo 的名字组成。导入时，Lean 建立一张以全局 Name 为键的模块索引表。它依导入顺序用 insertIfNew 登记 kernel 常量，也用 insertIfNew 登记 IR 中的 extraConstNames。对部分同名、同类型、同宇宙参数的兼容声明，subsumesInfo 允许继续导入。即使替换了常量代表，该索引仍采用首次登记的所有者。getModuleIdxFor? 直接查询该单值表。因而某模块序列化的全部名称与按全局首次所有者分组的集合，在任意合法导入图中没有无条件相等的保证。Round6 还使用 env.find? 过滤没有 ConstantInfo 的条目。以上是可导致两种计数概念分离的机制，现有记录尚未指明哪种机制涉及本次 FinitePiIntegral。锁定 Environment.lean 的原始 SHA-256 为 `ee364e4788ce0560c87f621eeb3c4c3dfec62e8db4e15e099fd80e6adc533b86`。 [模块数据](https://github.com/leanprover/lean4/blob/62eed1db4d67327ec8120be05f1a1b0847d74561/src/Lean/Environment.lean#L114) · [归属查询](https://github.com/leanprover/lean4/blob/62eed1db4d67327ec8120be05f1a1b0847d74561/src/Lean/Environment.lean#L1195) · [兼容条件](https://github.com/leanprover/lean4/blob/62eed1db4d67327ec8120be05f1a1b0847d74561/src/Lean/Environment.lean#L2268) · [导入循环](https://github.com/leanprover/lean4/blob/62eed1db4d67327ec8120be05f1a1b0847d74561/src/Lean/Environment.lean#L2332)

## 最小诊断改动

仅在 P4 生成器产生的现有 `unless owned.qsort Name.lt == data.constNames.qsort Name.lt` 失败分支中，在原 throwError 前打印并刷新一条 `P4_INVENTORY_MISMATCH` JSON。保留原立即失败路径，成功记录和 Core 驱动可沿用原字节。

1. 输出目标模块名、循环 idx、getModuleIdx? 返回的实际索引和 moduleNames[idx]，以及 isModule、importAll、hasData。
2. 输出已排序的完整 owned、data.constNames 和双向带重数的差异。原 gate 比较数组，诊断也须能区分重复次数。名称若含数值私有组件，保留 Name.num / Name.str 的结构，便于无歧义回读。
3. 对每个差异名输出 env.find? 是否存在、getModuleIdxFor? 的结果及对应模块名，并记录所有 header.moduleData 的 constNames 中出现该名的模块索引。若输出 main ModuleData.extraConstNames，应明确其来源；Lean 实际 ownership 导入还读取 irData，不宜将二者在所有导入模式下视作同一张表。

继续要求完整声明清单相等、全类型、定义模块及仅标准传递公理。在获得冲突名和所属关系之前，P4 的完整声明验收仍失败。此次仅核读失败日志、仓库原始对象及锁定 Lean 源码，未运行本地或远端证明。
