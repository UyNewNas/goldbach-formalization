# lower_square：实际已选素数前缀的整数平方门槛

已完成一个闭合文本的 source-only 模块 `P2OriginalSelectedIntegerPrefixSquares.lean`（10 个定理），未编译，正式信用为 0。分配的整个 L5/L6 原生 rho 支持绑定任务尚未完成。

本次消除的是“同一个已选分支的实际逐素数平方门槛如何变成整数不等式”这一义务。代码沿用 `selected_source_actual_square_gates`，从实际 `select` 的唯一分支 `b` 取 `SourceForm.supportMask` 与该分支自己的 `bufferedCap`，不使用普通 Trace 的全 false 标记，也不替换成理想父 cap。实际自然数素数向量取 `coordinate N (p i)`，标签直接沿该真实 code 与 supportMask 生成。

证明先复用已有 `physicalWord_power` 和 `coordinate_power`，把带初始乘数 B 的 `SquareGates cap T` 逐项转成整数 `B * p_j^2 <= N^cap`；每前进一步，B 精确乘上当前素数。完整测试以 B=1 开始；选中补集测试以原始选中素数的实际乘积开始。另给出索引形式，输出 `B * prod(take i) * p_i^2 <= Q`，并证明选中乘积与补集乘积恰为完整乘积，重复数值也不丢失。

最后，每个实际素数大于 1，因此末槽完整平方界严格大于完整前缀乘积；这给出真实前缀乘积 `< N^bufferedCap`。此处不要求把整个 rough 因子平方。

核对原稿 280–297、808–817 行后，必须保留一个区别：原稿列的是每个 prime slot 的前缀平方与选中补集平方；PhaseB 的 `(b*s)*r^2<Q` 是更强的充分前提，不能通过重写把它认定为原稿逐槽门槛的直接结论。本次没有声称原稿有数学缺口。

仍缺的内部衔接：构造覆盖实际 L5/L6 分支的有限 bank（含 W-winning chamber）；把本模块的实际带标素数向量与 native rho 的 small/rough 质因子、冻结父历史、SourceForm licence 完整对应；在相同总 Q 下加入 small Rosser 和全部 rough descendants，保存 full 与 selected-complement 两组门槛；再向同一 signed rho 的 AP/BV/PP 及 lower mean 接口交付。新文件没有把这些结论改名为假设来宣布任务完成。

导入边界：`P2OriginalSelectedMaskPhysicalSquares` 仍为 source-only 文件，需按 REGISTRY.json 中安装映射及 SHA 提供给编译专员；不声称已生产安装。另两个直接/传递生产依赖的精确 SHA 以及所有引用前驱已登记。只写本任务目录，未改生产源码、旧草稿、Git index、看板；未跑 Lean/lake、数值 checker、测试或额度检查。