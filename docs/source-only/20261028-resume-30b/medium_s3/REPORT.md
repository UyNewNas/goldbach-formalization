# medium_s3 第二批：全局半开 dyadic ownership 与实际 canonical 重索引

输出两份完整局部源码，共 537 行。`Part3MediumGlobalDyadicOwnership.lean` 定义原始 retained 物理模数对与 installed row label 的六坐标 dyadic key。六坐标是 s、t、u、v、d=st、w=uv 的 log2。区间严格采用 `[2^k,2^(k+1))`，unit 1 归 k=0，上端点只归下一块。通过实际 owner 的有限像构造 bank，并从原始 Q2/Q3 support 推导全 bank 基数至多 `(Nat.log2 physicalCap + 1)^6`。bank 不依赖 m、beta 标签 n、系数或同余条件。

它证明各块无交、唯一 ownership 和复权重求和恒等式，接到真实的 `atom.complexRowLabels`，完整保留 q1、beta n、gamma 和 `deletedCongruence`。retained W 的两个平方因子使用两份独立 key，仍共享同一个 m；交叉项完整保留。

`Part3MediumOwnedCanonicalReindex.lean` 把半开整数区间精确转换成第一批 receiver 的闭整数窗 `[2^k,2^(k+1)-1]`。物理 `ownedSlice` 先由原始 retained carrier、owner 和实际 d/w 定义；证明其与 `fixedBlock.selectedModuli` 加 smooth trim 双向等价，然后证明为 `trimmedChoices` 的无碰撞像。全部 exact d 和 w 在同一 dyadic key 内部求和，没有把 D 个 d 当作 D 个独立分布余项。最后给出整个 retained installed row 的全局 canonical 重索引，并直接特化到真实 deleted progression row。

“有限全局半开 ownership + 第一批 canonical fixed-block 真实重索引”局部源码步骤已写完，记录为 local_step_complete=true、assigned_next_step_complete=true。按原完整目标口径，task_complete=false、original_batch30_task_complete=false，完整 S3/medium 仍 OPEN。本稿没有把原 installed W 的两份 q1 或 d 相等作为结论；建立共同 q/d 的原始 preliminary Cauchy/dispersion 顺序仍待衔接，也没有给出 smooth-tail 剔除的 Shiu/Rankin 估计、全部 off-diagonal/gcd cutoff 或 Rcal*(N+Y) 恢复界。

未发现原稿缺口。未改第一批或生产源码，未编译、未执行 checker、未查额度，正式信用 0。所有本轮源与第一批 frozen import 的精确 SHA 见 REGISTRY.json。源码检查未发现证明占位符；这不等于内核通过。
