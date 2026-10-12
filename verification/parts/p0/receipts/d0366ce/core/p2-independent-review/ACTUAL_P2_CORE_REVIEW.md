# P2：d0366ce 实际核心归档的独立核对

## 结论与范围

**本次实际核心导出的 P2 三模块共 400 项声明，与已接收 producer 的 400 项在 `name`、`module`、`kind`、`type`、`readable_type`、`axioms` 六个字段上全部精确相等。** 本次原始 Round4 `stdout.log`、归档 `declarations.json`、阶段日志和完整 job log 中的 414 项声明逐项对应；其中另外 14 项属于 P1 许可模块，本回执不据此声明它们与某个旧 P1 producer 的类型相等。

类型比较没有进行空白规范化、结构化简、重排参数、替换名字或省略隐式参数。本次五个完整 `pp.all` 类型已从实际 d036 核心归档提取，见 [ACTUAL_CORE_FIVE_PP_ALL.md](ACTUAL_CORE_FIVE_PP_ALL.md) 和 `actual-five-ppall/` 中五个原文文件。它们现在有本次实际编译器输出支持，不再仅引用早先 producer；原先注明当时核心类型待导出的文件保持原样。

独立检查的状态为 `PASS_ACTUAL_CORE_P2_400_EXACT_RECORD_COMPARISON`，现有回执记录 **1318 项检查通过、0 项失败**。这表示本回执限定范围内的证据核对通过。完整核心消费、Round3 的 198 项类型及最终总回执由 P0 根代理统一负责；本次没有再次启动 Lean、CI、内核重放、网络请求或核心消费者。

## 固定版本与原始证据

| 项目 | 实际身份 |
|---|---|
| 集成源码 SHA | `d0366ce64272e81faf6166a8a90050f56b328d38` |
| 集成 tree | `e2ab22b96f76c8969386296558c626c62a581700` |
| P2 producer 证明 SHA | `f0c00f9ccce98e04af439321a92eb9fd0dd26203` |
| P2 producer CI 源 SHA | `e6d6d57323cc358cef060fb243ec386c13cb662d` |
| P2 固定交接 SHA | `101bb2291cd51f9717544ce477122fdd44eda44d` |
| 实际核心 run / attempt | `38289734671` / `1` |
| 实际核心 job | `114946653833` |
| 实际核心 artifact | `11767708658` |
| ZIP | `543994` bytes；`38` 个文件成员 |
| ZIP SHA-256 | `4d7499fd526651d70f73fb7cbbf98769ffc51d8a406e1bc80f96ad5dc0d20df8` |

原件目录为 `/workspace/scratch/535d89efd063/p0-round4/d0366ce-ci/core/`，包含 `core-artifact.zip`、`run.json`、`jobs.json`、`artifacts.json`、`job.log`。这些文件没有被修改。

归档内本次 Round4 类型目录为：

```text
goldbach-formalization/goldbach-formalization/.lake/part0-round4-types/20261012T191316121045Z/
```

已核对 metadata 中的固定源 SHA、run、job、artifact 以及 run/job 的 `completed / success`。六个必需步骤均有实际开始、完成时间和 `success`，不是尚未调度或跳过的步骤：

| 实际步骤 | 开始 UTC（2026-10-12） | 完成 UTC |
|---|---|---|
| Build the full project | 18:17:58 | 19:01:59 |
| Check the four explicit round 4 production targets | 19:01:59 | 19:02:03 |
| Recheck ImbalancedChen with bundled Lean 4.33.0-rc1 leanchecker | 19:02:03 | 19:09:40 |
| Audit ImbalancedChen root declarations and transitive axioms | 19:09:40 | 19:10:09 |
| Export complete round 3 types and the existing conditional main bridge | 19:10:09 | 19:13:16 |
| Export complete round 4 types and the existing conditional main bridge | 19:13:16 | 19:16:24 |

实际 Round4 回执记录 `lean_invocation_started = true`、`lean_exit_code = 0`、`pin_check_exit_code = 0`、`full_types_untruncated = true`，失败列表为空。调用是锁定环境中的严格 Lean 调用：

```text
/home/runner/.elan/bin/lake env lean -DwarningAsError=true -o
/home/runner/work/goldbach-formalization/goldbach-formalization/.lake/part0-round4-types/20261012T191316121045Z/Round4Audit.olean
verification/parts/p0/Round4Audit.lean
```

以上按参数换行展示；实际命令数组保留在原始回执。调用耗时 `186.541` 秒，继承的 Lean 搜索路径已清空。类型导出步骤本身没有再次构建或重放生产模块；生产编译、四个明确目标与 bundled checker 重放属于前面实际执行的独立步骤。

## 逐项一致性

| 所属模块 | 实际声明数 | producer 六字段逐项相等 |
|---|---:|---|
| `ImbalancedChen.Certificates.PairedV2Batch4To64Data` | 72 | 72 / 72 |
| `ImbalancedChen.Certificates.PairedV2Batch4To64` | 207 | 207 / 207 |
| `ImbalancedChen.Certificates.PairedV2Prefix64` | 121 | 121 / 121 |
| P2 合计 | **400** | **400 / 400** |

这些数量包括审计清单中的生成声明与私有声明，不仅是手写定理标题。当前所有 414 个名字唯一，四个模块计数标记及总计 414 的结束标记一致。

`COMPARISON_400.json` 为每个 P2 声明保留六字段比较结果、两端完整类型 UTF-8 SHA-256、原始 stdout 和完整 job log 的行号、字节偏移、原始行散列及外层前缀。`TYPE_DIFFERENCES.json` 是实际空数组 `[]`。

对应关系检查到以下层次：

1. 归档内 414 项 `declarations.json` 记录等于原始 stdout 中解析到的 `P0_ROUND4_DECL` 记录。
2. 原始 stdout 完整字节串未经修改出现在阶段日志内，阶段日志的 414 项也逐项一致。
3. 完整 job log 中的对应 marker 载荷与 stdout 的 marker 字节一致；仅识别并分离日志系统添加在 marker 之前的时间戳和可选 UTF-8 BOM，载荷与类型内部的任何字符均未转换。
4. P2 的 400 项再与固定 producer 的编译器记录逐项比较，六字段全部相等。

producer 比较原件为 `p0-round4/p2-intake/fixed-source/verification/part2/round3/batch4-to64/compiler-types.json`，SHA-256 为 `882a111f3bbf5bdc902ffd00aa52565f99cccaa027f2ecb6ffd8075889925cd4`。实际 d036 的完整 414 项 JSON SHA-256 为 `ff69058b10238439f752bb9f54e94da9b0e28e3ba1e5e03f55fef13355c2ce53`。本目录中 400 项实际记录的 JSON SHA-256 为 `5f36ebd40258e9ff1c2da6e9f85b79fba9e89104e3ffc77170d6bde79f17e57c`。

## 五个实际接口与公理

以下名字均以完整命名空间 `ImbalancedChen.Certificates.PairedV2.Prefix64` 为前缀；源码没有供本回执引用的 `pairedV2Prefix64_*` 别名。完整类型使用 [ACTUAL_CORE_FIVE_PP_ALL.md](ACTUAL_CORE_FIVE_PP_ALL.md) 中的实际原文，不以源码可读头部代替编译器输出。

| 定理名后缀 | 完整类型 UTF-8 bytes | 类型 SHA-256 |
|---|---:|---|
| `integral_semantics` | 4792 | `68a4f4c2142258e10edce3068e0089f5db16654d3e56a303d30101776e985166` |
| `integral_bounds` | 379 | `8bc7d0cc65a190283c3aa58bc609a297ca1f850e3b4207e7464e446f6a3a5e57` |
| `integral_eq_parts` | 256 | `11d44db197a95929e5af5beca5254a016fc2d9d9d001f1dfe85b931e060eb140` |
| `source_ordinal_coverage` | 647 | `96c8f524d71a0fc0a747a1b5b83de2e1f3daafe0c1b8b316ec1aac80a3493e09` |
| `rowIndices_injective` | 177 | `65e0bb67b146e40ab643a3e810ad73ef578ef2648a6b796fa5cceae186499d91` |

`source_ordinal_coverage` 的实际传递公理列表是 `[propext, Quot.sound]`；其余四个是 `[propext, Classical.choice, Quot.sound]`。这些列表与 producer 精确相等。实际类型导出回执记录 `unsafe_and_new_axiom_checks = PASS_IN_LEAN`；本次证据消费没有通过重新解释或简化类型改变这一检查的范围。

五个实际类型分别陈述 64 格的四重实积分语义、上下界、旧 4 格与新 60 格积分的精确相加、源序号的 `n < 64` 覆盖、以及 `rowIndices` 的单射性。唯一带显式变量的上述定理是 `source_ordinal_coverage (n : ℕ)`；完整量词、隐式参数、实例与 universe 参数以本次原文为准。

## 源码身份与对象身份的区别

通过只读 `git show d0366ce64272e81faf6166a8a90050f56b328d38:<path>`，三新增模块与九供应模块共 **12 个固定源码文件**均与 producer 原件逐字节相同。实际类型导出的 `inputs_before` 与 `inputs_after` 整体一致，包含 274 个源码记录和 267 个生产对象模块映射。

这 12 个 P2 文件中，**9 个**在本次类型导出的源码/对象快照中有记录，包含三个新模块的全部 400 项声明。另三个旧供应模块 `RationalLogCertificate`、`PairedFibreIntegral`、`PairedCertificateChecker` 不在这一特定导出快照内；本回执对它们只声明固定 Git 源码身份相同，不补造对应对象散列。详细分层保存在 `SOURCE_OBJECT_BINDINGS.json`。

三个新模块的源码散列如下，均同时匹配固定 d036、producer 和本次导出快照：

| 模块后缀 | 源码 SHA-256 |
|---|---|
| `PairedV2Batch4To64Data` | `4cf955fd381af6b405daa00dba827aada4f174eedda152ccd5de7b15cdaa5b0c` |
| `PairedV2Batch4To64` | `c8f78bbb79fc111aaad09ac49f0685bc51d37e67171418290cab9cd8b7724cb4` |
| `PairedV2Prefix64` | `11b0d1bf69c25abf05256eb0e6d52b2c743d37b47650a15ba6da90e2a453d7da` |

**新旧三个生产 `.olean` 的记录散列均不相同。** 类型与源码相同不能改写成生产对象字节相同，也没有推断散列变化的原因：

| 模块后缀 | producer 记录的 `.olean` SHA-256 | 本次实际记录的 `.olean` SHA-256 |
|---|---|---|
| `PairedV2Batch4To64Data` | `61b3d3eeef416c6293ebdba0b5b1ac89a1d0d44e99be316f6139c2d51d60b259` | `9443596de53ed0afbc00577d45c6b60472519b71691154542db17302fcda8c1a` |
| `PairedV2Batch4To64` | `6beb6f075f9d8539026bdd18716d9f3e6175a7253ec04244f7b1f8bf80637562` | `146854fdd1b8ff4346274a39020415558e162577e3237e64c8bfc8189e30b91a` |
| `PairedV2Prefix64` | `43adce492a503e2fc3bae8ab1d5f1e2586f17f20307bb1bc78258a2810436bca` | `5baa65e6a536072cbfc5fdc816a0ab5b60f845a44ccd031ffcb2d6acc23f4443` |

当前归档不包含这些生产 `.olean` 的实际字节，包含的是真实运行记录下来的散列。本次新生成的审计输出 `Round4Audit.olean` 则有归档原字节，已与回执散列核对，其 SHA-256 为 `a3e842e7aa202c49cde7d4ce6c8ba1f06c2e3e7054fb2ed17d1f0dc0e6cb8bc3`。

实际 bundled checker 日志对三个新模块均有 `replaying <module>` 标记。对象快照是在随后类型导出时取得；重放日志未在同一时刻打印对象散列。因此本回执分别陈述实际重放模块标记和随后未变化的类型导出快照，不声称日志直接展示了重放时对象的逐字节散列。

## 解析过程中保留的真实诊断

两次本地纯证据检查的失败均已封存，不是 Lean 诊断或 CI 失败：

- 第一次只识别时间戳前缀，完整 job log 第 7633 行的外层时间戳前还有一个 UTF-8 BOM，导致只识别 413 / 414 项。缺少的是私有生成声明 `...Batch4To64.rowIndices.match_1.eq_31`；已有 413 项没有字段差异。随后仅允许日志时间戳前的可选 BOM，未改 marker 载荷。原脚本、回执与诊断保留在 `attempts/001-before-external-bom-prefix-support/`。
- 第二次额外假设全部 12 个供应/生产模块都存在于此导出快照，读到缺失的 `RationalLogCertificate.lean` 键时停止。随后对三个新增模块仍硬性要求完整快照，同时把缺少快照的三个旧供应明确记为仅固定源码身份；原件保留在 `attempts/002-before-explicit-snapshot-scope/`。

上述修正都没有修改原始证据、类型、公理或生产源码。当前脚本为 `review_actual_p2.py`，SHA-256 `7220d00fd7519d1666a73493b6efd13c49f1b09dbf7530b2912ca12c02a1c64e`。其最近一次纯本地运行返回 0，检查清单保存在 `CHECKS.json`，没有为整理此说明再次运行。

## 接收结果与未闭合输入

本次证据支持 P0 对这三个已集成 P2 模块及 400 项实际类型的验收。可供后续 P1 / P4 / P5 使用的是固定 same-mask-v2 的 **前 64 个源序号**结果：旧 `0–3` 四格与新增 `4–63` 六十格相加，单射和序号覆盖支持没有重复计入旧四格。64 格上下界为

```text
[203256527543633, 203256645234388] / 10^20.
```

这不是整个 17572 格证书的上下界。仍未由此关闭的输入包括 E0 的 `[64,6091)`、E1 的 `[6091,17572)`、完整 mask 与保存下界的语义估计、P1 完整历史选盒及真实几何构造、实际计数到积分的误差桥，以及 P3 / P4 / P5 的分布和分析供应。这里的有理数 `K` 参与局部积分系数，不能仅凭这批有限格证书宣称实际同一 `rho` 的解析 `K` 密度界已完成；`c`、`hLower`、`hUpper` 也未被这五个定理关闭。

实际 Round4 回执继续明确记录 `final_bridge_is_conditional = true`、`hLower_hUpper_discharged = false`。本次验收没有新增包装来隐藏这些输入。Part 5 对 Part 4-A 的依赖仍独立于 Part 4-B。

## 文件索引

| 文件 | 用途 |
|---|---|
| `REVIEW_RECEIPT.json` | 本次独立核对的身份、结论、来源散列及范围 |
| `CHECKS.json` | 1318 项实际纯证据检查 |
| `COMPARISON_400.json` | 每个声明六字段比较及原始 stdout/job 字节位置 |
| `ACTUAL_CORE_P2_400_RECORDS.json` | 本次实际核心的完整 P2 400 项记录 |
| `ACTUAL_CORE_FIVE_RECORDS.json` | 五个实际接口的完整记录和公理 |
| `ACTUAL_CORE_FIVE_PP_ALL.md`、`actual-five-ppall/` | 本次实际五个完整 `pp.all` 类型 |
| `SOURCE_OBJECT_BINDINGS.json` | 12 源码逐字节身份、9 快照绑定与 3 仅固定源码范围 |
| `ACTUAL_ROUND4_RECEIPT.json`、`actual-round4-stdout.log` | 归档原字节副本 |
| `TYPE_DIFFERENCES.json` | 实际类型差异列表；当前为空 |
| `attempts/` | 两次本地证据解析失败原件，未覆盖 |
| `MANIFEST.json` | 本目录所有交付文件（清单自身除外）的完整字节数及 SHA-256 |

本说明不替代生产者原始回执或 P0 最终核心回执，所有原件与先前说明均被保留。
