# Review request: one actual singleton medium window

审查对象仅为本目录冻结的 `P1OriginalSingletonMediumWindow.lean`。这是原稿内省略的有限尺度及统一阈值推导候选，未编译、未宣称 kernel 或递归闭包通过。请保持旧 route-only fcb1d83/e406a828 和其他源不变。

请重点核对：

1. `live_geometry` 真正读取 `integerProfile kap 6 N cj kap0` 的 eta/psi/ambient；cap 为 2N，trim 与剩余目标为 N，完整补积而非遗漏短因子的商。
2. 仅复用 P4B `tuple_scale/fibre/same_scale` 的任意槽数声明；没有实例化两组 RealB profile。新单组常数是 `1/4, 2, 8, 2`。
3. 原 firstMedium 选位置的时序，重复槽/重复 block 不合并；活点只用来推出整个同 fibre 的尺度，不能删掉 profile 零点上的 Fourier 项。
4. fixed `K,kap,zeta,kappa,kap0,xMin` 先于 N threshold，后者先于 cj、r、bs、i、C。三种 kappa 的角色不可混同；same cutoff 恰为 `roughF(2^(6K+3)R cj)`。
5. 幂吸收与 residue range 的所有常数正性，尤其 `2U≤x`、`x≤v≤x²`、`roughF x≤roughF v`；没有 `hDesiredWindow` 或目标误差前提。
6. REPORT/EXACT_BOUNDARY 是否准确保留 whole-box 四条、signed M、singleton roles/band/restoration、历史 middle/full87 的 HOLD；新 half-J 已有原范围源 AL，不能再声称其 hJ 参数未付，也不能视为全 M 已付。

三条直接 import 的精确 existing source 身份已嵌入 `SOURCE_PINS.json.direct_imports`。其他 proof-bearing key declarations、profile原像、最终 caller 和手稿按原始字节绑定在同一清单；不把这些记录称为完整递归 source closure。candidate 共三个公开 theorem 和一个 private 数值 helper，无 axiom/sorry/admit；该静态事实不替代 elaboration。

