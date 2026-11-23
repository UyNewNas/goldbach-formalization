本记录覆盖七个依赖模块、共 215 个公开声明的检查。三个 U7 模块分别检查 30、6、21 个声明，连续筛模块 15 个，三个 Member 支撑模块共 143 个。U7 源码对应 1106 版手稿的第七积分原三角域，边界为 `59/250 ≤ t ≤ 1/3`、`t ≤ u ≤ (1-t)/2`，分段接缝为 `u=(1-t)/3`。手稿固定到 `a988cba584d803ae2856a0de50efb582f4f3dd6a` 的 `paper/release-20261106/en`。

原构建在行积分的连续性组合处达到 4,000,000 heartbeat 上限，两处积分字典改写还保留了函数应用形式。修补显式给出配对映射、映射到正象限的证明与 `ContinuousOn.comp'` 的函数参数，并在分支改写前用 `change` 展开定义相等的条件表达式。复用了原来的全部定义、数字常数与 30 个公开声明。源码的状态注释指向本目录。

| 检查 | 实际结果 |
| --- | --- |
| 标准 Lake 模块编译 | 退出码 0 |
| 指定模块的独立 kernel replay | 退出码 0 |
| 30 个公开声明的完整类型与传递公理 | 退出码 0 |
| 公理集合 | `propext`、`Classical.choice`、`Quot.sound` |
| 独立源码复核 | 两处证明修补无问题记录 |

使用 Lean `4.33.0-rc1`、Mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1` 与 goldbach `09b97db5764ade1246bfb77206baa1b124760958`。源编译保留 `-t0 -j2 -M12288`、`maxRecDepth=100000` 和 `maxHeartbeats=4000000`。复核覆盖指定模块及其现有导入环境。

本次验证工程为 `/workspace/blue-p6-build`，基础依赖选自已登记的 `R02_SOURCE_SELECTION.json`。Omega 模块使用本目录登记的生产源码后像。以下命令通过仓库现有 T01 `ci_runtime_guard.py` 创建的工具链包装执行。

```sh
lake build ImbalancedChen.P5U7OriginalOmegaIntegral:olean
lake env leanchecker -v ImbalancedChen.P5U7OriginalOmegaIntegral
lake env lean -DmaxRecDepth=100000 -DmaxHeartbeats=4000000 /workspace/goldbach-formalization/docs/verification/20261123-blue-compilation/OmegaAudit.lean
```

源码选版、实际编译器命令、五项产物摘要、检查退出码与日志摘要见 [OMEGA_RESULTS.json](OMEGA_RESULTS.json) 和 [OMEGA_SOURCE_SELECTION.json](OMEGA_SOURCE_SELECTION.json)。检查驱动见 [OmegaAudit.lean](OmegaAudit.lean)。

另外两个支撑模块各修补一处证明中的 API 用法。Buchstab 的有限差分证明使用当前 Mathlib 的 `abs_add_le`。Fubini 证明先用 `dsimp only [B]` 展开局部矩形集合，再改写乘积测度。两处修补保留原声明、定义、常量与假设。源码状态注释已更新。

以下命令在同一工程与 guard 下实际执行成功。两个模块均通过独立 kernel replay，27 个公开声明的完整类型与传递公理检查也通过，观察到的公理仍只有 `propext`、`Classical.choice` 和 `Quot.sound`。独立源码复核无问题记录。

```sh
lake build ImbalancedChen.P5U7OriginalBuchstabLipschitz:olean ImbalancedChen.P5U7OriginalOmegaFubini:olean
lake env leanchecker -v ImbalancedChen.P5U7OriginalBuchstabLipschitz
lake env leanchecker -v ImbalancedChen.P5U7OriginalOmegaFubini
lake env lean -DmaxRecDepth=100000 -DmaxHeartbeats=4000000 /workspace/goldbach-formalization/docs/verification/20261123-blue-compilation/OmegaSupportAudit.lean
```

这两个模块的结果与产物摘要见 [SUPPORT_RESULTS.json](SUPPORT_RESULTS.json)，选版见 [LIPSCHITZ_SOURCE_SELECTION.json](LIPSCHITZ_SOURCE_SELECTION.json) 和 [FUBINI_SOURCE_SELECTION.json](FUBINI_SOURCE_SELECTION.json)，检查驱动见 [OmegaSupportAudit.lean](OmegaSupportAudit.lean)。上述记录按实际执行的模块与命令分别保存。

连续筛模块 `P2ContinuousSieveRational` 的三个证明补充了振幅 `A` 的定义展开、乘法与除法的结合归一化，以及 `sub_div` 归一化。15 个公开声明及三个定义保持原样。它是首带有理包围与保守尾界的支撑模块；其余表格递推和最终数值积分的验收另行记录。本轮未发现实质数学缺口。

该模块在同一 P6 工程和 guard 下完成以下三项检查，退出码均为 0。类型与公理检查的标准输入逐字保存在 [P2ContinuousSieveAudit.lean](P2ContinuousSieveAudit.lean)，公理名称的宇宙参数只在汇总时归一化，原始输出完整保留。

```sh
lake build +ImbalancedChen.P2ContinuousSieveRational:olean
lake env leanchecker --verbose ImbalancedChen.P2ContinuousSieveRational
lake env lean -DmaxRecDepth=100000 -DmaxHeartbeats=4000000 --stdin < /workspace/goldbach-formalization/docs/verification/20261123-blue-compilation/P2ContinuousSieveAudit.lean
```

结果、15 个完整类型与传递公理、五项产物及实际编译器命令见 [P2_CONTINUOUS_SIEVE_RESULTS.json](P2_CONTINUOUS_SIEVE_RESULTS.json)，选版见 [P2_CONTINUOUS_SIEVE_SOURCE_SELECTION.json](P2_CONTINUOUS_SIEVE_SOURCE_SELECTION.json)。源码及五项产物在 kernel replay 和声明检查前后保持一致，公理集合仍限于上述三项。原失败与成功日志均保存在本目录。

Member 工程使用同一组 Lean、Mathlib、goldbach 固定版本，基础项目选源来自 `R03_SOURCE_SELECTION.json`，并使用其独立的现有 `-t0 -j2 -M12288` guard。以下两条标准构建命令均退出 0，三个模块也分别通过独立 kernel replay。

```sh
lake build ImbalancedChen.CurrentChenUpsilon1011JointSource:olean ImbalancedChen.CurrentP5MarkedElevenWitnessSource:olean
lake build ImbalancedChen.P5OriginalActionMassBound:olean
```

`CurrentChenUpsilon1011JointSource` 完整复用既有提交 `86d2a123d08befe29c69454637fa9aa1d2614441` 中的源码，补全有限和筛选表达的归一化。`CurrentP5MarkedElevenWitnessSource` 在 `subst` 前将投影等式定义展开为 `j = i`，并更新状态注释。两模块的 34 个公开声明均通过完整类型与传递公理检查；结果与原始日志见 [member-current/RESULTS.json](member-current/RESULTS.json)，选版见 [member-current/SOURCE_SELECTION.json](member-current/SOURCE_SELECTION.json)，驱动见 [CurrentSourceAudit.lean](member-current/CurrentSourceAudit.lean)。

`P5OriginalActionMassBound` 的七处证明修补使用 `setIntegral_const`、显式 `Fin 2` 坐标序链和集合参数，保持 109 个公开声明及全部定义、常量、假设不变。109 个完整类型与传递公理检查通过；结果见 [ACTION_MASS_RESULTS.json](ACTION_MASS_RESULTS.json)，选版见 [ACTION_MASS_SOURCE_SELECTION.json](ACTION_MASS_SOURCE_SELECTION.json)，驱动见 [ActionMassAudit.lean](ActionMassAudit.lean)。原阶段记录证明源码及四项输出 `.olean`、`.ilean`、`.c`、setup 在检查前后稳定；`.trace` 另记为全部检查后的独立当前快照，没有跨阶段比较。结果解析器只修正了标准公理名称的宇宙参数归一化，没有重跑成功的 Lean 命令。

上述三个 Member 模块的公理集合也仅包含 `propext`、`Classical.choice` 和 `Quot.sound`。原始日志保留 Lean 的输出空白格式。各入口的最终验收与单个依赖模块的检查分别记录。

项目看板本轮读取返回 HTTP 401，完整蓝色节点到模块的对应清单仍待取得。第七积分入口和 H430 Member 入口的后续构建另行记录。
