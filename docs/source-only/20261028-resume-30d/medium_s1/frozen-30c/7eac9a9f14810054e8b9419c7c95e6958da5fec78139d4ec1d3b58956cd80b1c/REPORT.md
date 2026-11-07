# 第三批 medium_s1：actual same-paperPsi common-m count

已冻结第二批三个文件的精确字节至 `frozen-30b/`，原文件未改；清单见 FROZEN-30B.json。新增两份 Lean：`Part3OriginalPaperPsiCoprimeCount.lean` 与 `Part3OriginalSamePsiS1Remainder.lean`。没有运行 Lean、lake、编译或 checker。

第一份源码从已写的实际 `paperPsiSchwartz` 与 actual-profile Poisson packet 出发，复用通用 Schwartz 二阶衰减和原有纯标量望远镜 lattice majorant，得到所有 `t>0` 的 nonzero packet 统一 O(1)。该常数在尺度、模数、任意有符号 residue 和有限支撑集之前选取，允许模数大于尺度。随后把 canonical profile 载体改为任意包含其实际非零支持的有限载体，得到真实 paperPsi 的 progression/multiples O(1)。借助已有纯有限 Mobius 恒等式，得到 `C*tau(q)` 的 coprime counting 误差。

零模质量定义为原稿的 `h0=integral paperPsi`，并从 Mathlib 的 Fourier 定义和 `integral_complex_ofReal` 证明 `Fourier(paperPsiComplex)(0)=h0`。未假设一个外来 mass 相等式，也未把旧 dyadic bump 重命名成 paperPsi。

第二份源码建立新的 actual same-psi `paperS1PurePair`、`paperS1PrincipalPair` 与 `paperS1RemainderPair`。精确 `MT+error` 保留原来的 `c_ell(r,s)`、两份 actual alpha coprime mass、同一个 common-m 模数 `ell*r*s`。新误差用第一份实际 paperPsi coprime count 支付，再由有限三重三角不等式进入原来已证明的同一个 `S1DivisorKernel`。全 d-block 也保留同一个 uniform counting constant。

最终 `actual_samePsi_fixedBlock_S1_bound` 将 m 尺度固定为原始 `B.atom.V`、取真实 `paperPsiNaturalCarrier`，并调用第二批绑定的 literal Lambda 与 q paperPsi，从而两端确实使用同一个构造出的 paperPsi。第一批发现的 q/m cutoff 接口差异在这个显式固定块实例已消除。

仍未完成原始全任务：全局 dyadic atlas 与块所有权、原始物理系数的全块精确重构、Y=QD 与多项式 caps 到 log(x)^C 的最终插入仍待证明；S2/S3 与 medium 全命题也继续开放。本轮未发现原稿数学反例。`local_step_complete=true`、`batch_target_source_complete=true`、原完整 `task_complete=false`、`compiled=false`、`formal_credit=0`。

固定版本 Mathlib API 只读核对： [Fourier 定义](https://raw.githubusercontent.com/leanprover-community/mathlib4/e4c91783ca8e6a7c693ae624ade32fd22d4e43c1/Mathlib/Analysis/Fourier/FourierTransform.lean)、[复数积分转换](https://raw.githubusercontent.com/leanprover-community/mathlib4/e4c91783ca8e6a7c693ae624ade32fd22d4e43c1/Mathlib/MeasureTheory/Integral/Bochner/ContinuousLinearMap.lean)。这属于源码 API 核对，不是本轮内核执行。
