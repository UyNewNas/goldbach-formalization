# Part 3 小批交接：整数长变量误差归一化

**接收 Part：Part 0。本批的三项局部门均已通过；范围严格限于原有两条归一化定理。**

## 固定来源

从本分支实际远程检查点 `7d70a2545fd819706e473eb41e4d430ad19119d8` 继续。发布前发现并完整保留并行提交 `9a720ba48c7bd82b674d68adf9b04cab0484b314`，该提交仅调整主 CI 超时；本批最终以它为父提交，证明源码与导入对象不受影响，详见 [publication-context.json](publication-context.json)。共同证明基线仍为 `1a80c1bcce67886f699d097fc37fd245cd3620bf`；Lean、mathlib、goldbach、手稿地图与完整 Part 3 验证门均未改动。

按 Part 0 固定提交 `80aca6710c83b5160f4c5fdd05d180e507990e95` 的 `verification/parts/p0/round2/ledger-final/MODULE_LEDGER.md` 接收 `Part3LongSlotDistribution.lean` 修复。接收源 SHA256 为 `67ccc48e6a4befadfd4b5639e2cdb4bd43e443b8f4eaf3086fe5a6c5fbd0023e`，与该提交的 blob `13288c1122f26135644bbd2c04f731f993ffa058` 核对一致。上游三门及 35 个定义模块声明的既有验收证据保留在 [upstream](upstream/) 和 [upstream-intake.json](upstream-intake.json)。未接收其他 Part 的生产修改。

## 实际验证

两条归一化定理的现有证明**首次严格编译即通过，源码无需修改**。本批只接收底层长槽的已有证明修复，并适配独立局部审计的 legacy 导入格式。

| 本批实际动作 | 退出码 | 工具执行秒数 | 结果 |
|---|---:|---:|---|
| 目标严格编译 | 0 | 9.477 | 原装 Lake 调用官方 `Lean.Elab.runFrontend`，`trustLevel=0`、`warningAsError=true` |
| 生产对象内核重放 | 0 | 2.785 | 原装 `leanchecker --verbose ImbalancedChen.Part3LongSlotNormalization`，有实际 replaying 行 |
| 全所属声明传递公理审计 | 0 | 15.226 | 审计源码严格编译；两条声明均仅依赖 `propext`、`Classical.choice`、`Quot.sound` |

这不是聚合 `lake build`，也没有重做整个导入闭包的 `--fresh` 重放。复用的 24 个 baseline 项目依赖来自同源、同版本、`trustLevel=0` 的既有成功对象；其既有普通诊断模式的编译不冒充本批重新严格编译。另一个项目依赖是 Part 0 已验收的长槽修复对象。

`audit` 实际执行三次：先后遇到 `import all` 要求 `module`、`module` 审计不能导入 legacy 目标的诊断，然后在保持生产模块原格式的局部审计上成功。两次失败源码快照、原始日志与退出码均保留。生产编译和重放各只执行一次。

## 精确身份与跨门绑定

| 对象 | SHA256 |
|---|---|
| `Part3LongSlotNormalization.lean` | `ca4e4d237bb4a5d21f72af3223001621902d6763d0b7ef1f423f532fd94f69fc` |
| 本批 `Part3LongSlotNormalization.olean` | `a74f51987d4e5ea037a2a9f9a5d9a74251ba7f697d4bede12f9252b9ef36a7e7` |
| 导入 `Part3LongSlotDistribution.olean` | `fd8cdcf5ac894e5b904f8bdc0e80506b16c23bb17bc1a568ea4a3a5b50b61816` |
| 导入 `BoundaryArbitraryLog.lean` | `2694e8398198c9edeab5f0c4bad70c514a22de21a0cec6edec33c2faec742167` |
| 导入 `BoundaryArbitraryLog.olean` | `8cbd34b16deaab526f918ab74193bf72ea7371c81ab1f0cb5470f1c127c85a4b` |

局部总回执程序化要求：严格编译产物与重放、审计的前后生产对象完全相同；三门目标源码相同；三门共有的所有导入源码和对象哈希相同。不是只合并三个通过布尔值。

生产依赖闭包有 **4,957 个模块**，各门前后实际计算 **29,642 个源码／对象部件文件**的 SHA256，包括存在的 `.olean.server`、`.olean.private`、`.ir` 和 `.ir.sig`。审计再加入目标源与目标对象，其实际环境共有 **4,958 个导入模块**；`env.header.moduleNames` 与 `Lean.findOLean` 给出的模块和路径与预期库存双向完全吻合。

目标采用 legacy（非 `module`）格式，只有一个完整 `.olean`。审计实际确认 `is_module=false`、`import_all=true`、`has_data=true`；定义模块声明集合与序列化的 `ModuleData.constNames` 集合完全相等，数量都是 **2**；`extraConstNames` 数量为 **0**。private/generated 内核声明没有被排除或按公开名称猜测。

## 类型与数学范围

完整原始 `pp.all` 类型、可读类型、声明种类及逐声明公理列表见 [compiler-declarations.json](compiler-declarations.json) 与 [COMPILER_TYPES.md](COMPILER_TYPES.md)。它们来自成功审计中的 `Meta.ppExpr info.type`，不是前两轮的源码提取候选类型。

确认的定理：

- `ImbalancedChen.part3_eventually_longSlot_logAccuracy`：对固定 `theta < 1`、自然数 `K`、`epsilon > 0`，最终同时对全部 `M D L U a` 和 `alpha rho`，由 `MD ≤ N^theta` 与两组实际支撑上的范数 ≤ 1 得到误差 ≤ `epsilon * N / log(N)^K`。
- `ImbalancedChen.part3_eventually_longSlot_singularNormalization`：相同条件下，最终误差 ≤ `epsilon * singularNormalization N`。

统一阈值始终位于所有区间、移动余数和系数之前。没有增加 `theta ≥ 0`、区间顺序或待证误差前提。物理模数仍为 `1 ≤ q ≤ D` 且 `(a,q)=1` 的完整集合。两条结论由已验收的 `2MD` 界及现有幂次间隙归一化供应者推出。

## 回执与证据

[receipt.json](receipt.json) 包含全部实际命令、环境、退出码、前后哈希、成功门与失败历史。[source-and-scope-guard.json](source-and-scope-guard.json) 记录打包时的源码扫描及完整门不变检查。

本批局部入口为 [run_local.py](run_local.py)，仅接受 `compile`、`replay`、`audit` 三个明确动作，不构建依赖；[finalize_local.py](finalize_local.py) 只绑定已经执行的记录并保存证据，不运行 Lean。实际执行参数：

```text
--runtime-config /workspace/scratch/e8f85e58ac36/tooling/round3/runtime-config.json
--output-dir /workspace/scratch/e8f85e58ac36/tooling/round3/execution
```

[local-evidence.tar.xz.b64](local-evidence.tar.xz.b64) 保存全部原始记录、完整导入哈希、源码闭包／复用对象来源、原装工具与驱动身份、编译器库存、失败历史和目标 `.olean`。[evidence-manifest.json](evidence-manifest.json) 给出压缩档与每个成员的 SHA256；打包后已逐个成员回读核对。仅解包证据：

```bash
python3 -c 'import base64,pathlib; p=pathlib.Path("verification/parts/p3/long-slot-normalization/local-evidence.tar.xz.b64"); pathlib.Path("local-evidence.tar.xz").write_bytes(base64.decodebytes(p.read_bytes()))'
tar -xJf local-evidence.tar.xz -C EXISTING_EMPTY_DIRECTORY
```

恢复的 runtime 配置保留本次真实绝对路径；另一环境应明确映射路径，并核对相应固定源与对象后再使用缓存。

## 接收边界

Part 0 可按本批独立固定提交、源码哈希与局部回执接收上述两条定理。完整 Part 3／全库门保持原样，本批不声称其余候选模块或完整解析分布通过。

仍待后续 Part 3 与实际 policy 接入：**rough／prime 长槽、长变量相位、Brun／Mellin 成本，以及论文实际参数推出 `MD ≤ N^theta`、`theta < 1` 的证明**。restricted medium、两长槽及实际完整上／下源的误差供应者不在本批新增验收范围。本批完成后即停止扩展。
