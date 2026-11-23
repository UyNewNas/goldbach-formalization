本记录覆盖三个 U7 模块的源码修补与 57 个公开声明的检查，包括 `P5U7OriginalOmegaIntegral` 的 30 个、`P5U7OriginalBuchstabLipschitz` 的 6 个和 `P5U7OriginalOmegaFubini` 的 21 个声明。源码对应 1106 版手稿的第七积分原三角域，边界为 `59/250 ≤ t ≤ 1/3`、`t ≤ u ≤ (1-t)/2`，分段接缝为 `u=(1-t)/3`。手稿固定到 `a988cba584d803ae2856a0de50efb582f4f3dd6a` 的 `paper/release-20261106/en`。

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

项目看板本轮读取返回 HTTP 401，完整蓝色节点到模块的对应清单仍待取得。第七积分入口和 H430 Member 入口的后续构建另行记录。
