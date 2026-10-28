# certificate_rows 交验报告

已写两份完整局部源码，原分配目标仍未全部完成；未编译、未执行 Lean/lake/producer/checker 或数值重放，正式信用为 0。

首先核对到 PhaseB 的 `P2Winner9ActualEightSimplexMoment.lean` 已有 actual Δ8 set-integral 到 nested moment 的 Fubini 源码，故没有重复该证明。本轮沿更新的 PhaseB4 真实物理顶点缺口推进。

`P2Winner9SelectedRowEdgeGeometry.lean` 复用已有 row21 raw vertex source，并逐字抄取原始 witness 的 row22 九顶点（ID 顺序 `[200,188,58,49,48,21,7,2,1]`）与 physical_volume。以第一顶点为原点、其余八顶点差为列，给出两行 `|det edge| = 8! * storedVolume` 的闭合 `decide +kernel` 源码，再由存储体积的正性推出两个矩阵非退化。这里的 `decide` 从未运行，因此这些是供编译专员执行的证明项，不能报告几何已内核通过。没有用 Python 计算或核对 determinant。

`P2Winner9PhysicalVertexInterpolation.lean` 是不依赖这些决定过程的实际代数连接：对任意九个真实物理顶点，证明 ordered-edge affine map 等于 barycentric interpolation；随后逐个证明 physical R、M、坐标和、gap、十个 factor、normalized factor、P、Y 与有符号 deviation 全部沿同一映射插值。最终得到原始 mixed polynomial 和 upper integrand 的精确插值表达式。常数 `-1/1000000`、全部十因子和乘子 `4` 均保留；不存在最终 moment law、目标 inequality 或 vertex-value matching 假设。这消除了 PhaseB4 物理 integrand 到其真实 vertex interpolants 的结构性推理义务。

剩余需从 rational edge 构造实 continuous linear equiv、转移 determinant 并实例化 physicalSupport/Jacobian；还需把真实 Y/deviation 顶点值绑到原 `SimplexData` 的整数尺度，然后才可使用已写 canonical mixed moment。两行 floor/cap、all22 与 17572 rows 均未闭合。当前没有发现原稿数学缺口；这是实现与 witness-binding 缺口。

所有读取依据、新源码 hash、声明名和安装映射见 REGISTRY.json。只写本任务目录，无生产文件、导入根、看板、Git 或旧源码变更。
