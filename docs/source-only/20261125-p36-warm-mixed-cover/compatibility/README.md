# warm-mixed 新 core 的原 owner 兼容拆分

状态：**仅兼容源码准备，未编译、未 kernel 验收、未安装到 canonical、未加入 target/manifest**。本目录是原冻结包的独立补充；原 `FREEZE.json`、5 份 Lean 核心源码及原有索引均保持其冻结字节。

## 四个 owner

| 兼容 owner | 原始固定版本 | 去掉并由新 core re-export 的声明数 |
|---|---|---:|
| `P2ActualPairPlanRawSupport` | 当前 main `4d1b2ed5abfe0772a8b3f1c52931a3f6f954cd27` | 2 |
| `P4AUpperTaggedFirstPrefixDisagreement` | P15 `c6b89774822580c731a236ac66dcd7466ac8a0e6`；当前 main 无原 owner | 4 |
| `P4AUpperTaggedFrozenAdmissionCatalogue` | 同一固定 P15；当前 main 无原 owner | 1 |
| `P5PresievedRoughSlotAffineGates` | 同一固定 P15；当前 main 无原 owner | 5 |

每份文件只增加 `import ImbalancedChen.P3OriginalU5WarmMixedReusedCore`，并删除已提取的原块。P2 的删除范围也包含紧邻第一条被移走 theorem 的原 doc comment，避免留下一段不再有所属声明的文档。其它原字节全部保留，原行尾不规范化。精确原路径、commit/blob/SHA、删块字节区间和新增 import 字节见 `COMPATIBILITY_PREPARATION.json`。

P2 特别使用当前 main 的原文件，而没有回退 P15 全文。原 `P2ActualPairPlanRunSupport` import 仍在；`PlanCeiling`、`step_cap_le`、`run_cap_le`、`accepted_run_sum_le` 的旧重复定义没有重新带回。其准备前 SHA256 为 `58e1a21d4d699012b73ca000bba101ce256d6f0b07c7191d271a488dd4419d85`，准备后为 `8e46a367aaf759d21980dd8395455bdb88fa4317b510a60397927f8fb71fa16f`。

## 已做的结构检查

对每份兼容文件，移除唯一新增 import，再在原字节偏移插回固定原文的删除块，均逐字节恢复指定原 owner。原文件中的两条 canonical-warm theorem 与已冻结 core 中对应块的关系，仍只包含冻结记录里的一个 `universe` 引用加引号适配；没有借兼容工作修改核心证明。

`IMPORT_GRAPH_CHECK.json` 使用明确的只读优先顺序：冻结新源码 → 本目录兼容 owner → 固定当前 main → 固定 P15。最后一层仅用于读取原 owner 的重型传递 imports，未复制或安装其 190 份额外源码。

- warm target 的项目源码闭包仍为 **269**。
- 新 core 的项目源码闭包为 **110**，不包含四个兼容 owner。
- 四个兼容 owner 均不在 warm target 图中。
- 对四个原 owner 的完整只读 imports 并图，共检查 **528** 个项目模块，没有 missing 或 cycle。
- 加载四个兼容 owner 后，12 个移出的完整声明名在上述源码并图中均只由新 core 声明一次。这是源码 namespace 检查，不是 Lean serialized inventory。

因此新增 owner → core 的 import 没有形成回环。上述 528 模块库存不是新的 build selection，也不是要求把这些重型依赖加入当前任务。未来主 tree 若需要保留这些完整 owner，应安装本目录对应的兼容副本；仅构建当前 warm target 时不应把它们列为新增目标。

所有检查仅涉及固定来源、字节逆还原和 imports 结构。原 owner 的剩余旧表达尚未由本任务编译验收；本目录不把旧 source-only 内容转换为 accepted proof。
