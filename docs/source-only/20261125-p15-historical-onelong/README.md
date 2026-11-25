# P1.5 两个历史系数差的单长素数项

本包是未编译的 Lean 候选。主声明 `exists_original_count_remainders` 在同一个充分大偶数阈值上给出两项原始计数的误差，每项都保留自己的显式复数余项。第一项使用原始 raw 减 licensed 系数，策略参数顺序为 `(S false, R false)`。第二项为第六层前驱减第八层更新，顺序为 `(eight false, six false)`。结论逐项保留原历史选择、三个遗漏预算、物理模数族、目标剩余类及其精确均值。

`retainedAtlas` 保留 `trimReserve + Σ(mediumAtlas + remainingTypeIAtlas − properPowerReserve)`。它对原单素数权、枚举上限 `2*N`、物理目标 `N` 求和。`eventually_history_remainder` 在原 `trueDDeltaSupport` 的 `remainingModuli` 上展开真实符号权，将去掉的原单长子和控制在任意固定的 `N / log(N)^A` 内。粗素数修正沿用逐图零和。源定理对单长子和只要求模数正、至多为目标的 599/1000 次幂取整、与目标互素及系数绝对值至多一。这些条件逐一由实际历史系数给出。

计数端取 `A=3`，将该费用和原 sharp 到 smooth 的费用各控制在半份预算内。最终界为两个实际计数各自减去精确均值、再减对应 `historyRemainder` 的范数至多 `u * singularNormalization N`。余项本身的算术估计、最终矩形的完整 singleton PP 和 P1.5 整体验收仍开放。

## 来源与验证

[源码绑定和缺失模块清单](SOURCE_BINDINGS.json) 记录了三个直接输入在 `3657bae7104407216eefc59dfa7a416fa76754e9` 的路径、Git blob 和 SHA-256，另列原素数分解、单长精确拆分、历史符号及归一化来源。对已索引的 OneLong 模块及 Y01 历史调用点定向复核后，原 OneLong 消费者含最终矩形两种通道，Y01 含两个历史的平滑余项，本包连接这两部分。

三个直接输入在该提交的标准模块目录均无同名文件。清单记录了按项目导入递归读取时，在本树对应路径找不到的模块、存在不同字节的候选，以及可在先前记录或指定历史提交取得的资料。完整输入版本尚待收齐并核对。未执行 Lean 编译、内核回放或传递公理审计。
