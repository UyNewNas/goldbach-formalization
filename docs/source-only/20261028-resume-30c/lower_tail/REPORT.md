# lower_tail 第三批

交付两份新 Lean 源码，共 605 行、27 条定理。前两批、生产源码、Git 和看板均未改动。

`P2UpperActualCompiledQueryBuffer.lean` 绑定真实联合 U10/U11 ordinary compiler 的同一 selectedPolicy、ownerBox、D 和 Z。它从 `D=N^physicalResidual`、`Z=N^cutoffExponent` 得到确切 `log D/log Z`，再消费该行原有 tau、xi、rho 参数字典，证明物理 max query 与理想 `max(2,R/w)` 的距离至多 `500*boxBuffer`。零 cutoff 的代数分支单独处理，没有从 `Z>0` 推断 `Z!=1`。

`P2UpperActualFiniteKnotMass.lean` 保留实际 `ordinaryTuples n N E`：低 U10 带不加掩码，高 U11 带保留原来的 E 补集。由真实四个不同质数证明其 product weight 正是 `1/phi(fullPrefix)`；由原始联合 source 的坐标范围证明全部质数落在具体紧质数宇宙。真实非 clamp 查询结点事件被选中 policy 的两个 affine cap side 之一覆盖，随后才对有限 16 个 policy 和两个 side 付费。一维闭区间 Mertens、原有 pivot/residual Fubini 及有限像求和给出明确 slabBudget，常数不随网格格子数量增长。

最终 `physical_actual_table_mass_le_clamp_add_mertens` 的结论为：实际物理普通源的有限结点质量，至多整个 `clampMass` 加上半径 `radius+500*meshBuffer` 的 slabBudget。这里没有删除 `q=2` 的整块 clamp。固定网格下物理 query 在一个 cell 上为常数，可以整块落在 knot；因此不能把半径中的网格误差省掉，也不能把 clamp 本身说成 O(radius)。这是实现所需的正确误差处理，未发现新的原稿数学缺口。

共同网格的误差也已具体化：计算得到 `meshBuffer=10*meshStep+21*eta/16`。取有理 `eta=meshStep` 后，它精确等于 `181*meshStep/16`，随网格加细趋零，并最终满足所有 N、所有质数元组共同使用的 `meshBuffer<=a/2`。没有把共同误差趋零作为新假设。

本批尚未闭合原目标：完整 clamp 的单边 cost 支付仍需接入既有 `BufferedOrdinaryClamp`，真实 fallback source 的 switched 支付、原始 H248 count/density 均值、共同 functional 收敛和 ordinary tail row 绑定仍开放。结点质量定理没有把 native rho density 认作静态 H248 score，也没有声称覆盖整个最终计数上界。

两份文件文本闭合，`complete_module=true`、`local_step_complete=true`；`batch_target_source_complete=false`、原始 `task_complete=false`。全部未编译、未运行 Lean/lake、内核、数值 checker 或 CI；正式信用为 0。实际直接导入及主要传递前驱的精确路径和 SHA-256 已登记，特别是 source-only `P2LowerUnrestrictedTupleStripFubini` 的 raw SHA `f6d43fe0842c6146c9154f4bf06ccf574a5815914207b81d9b3df42394578641`。
