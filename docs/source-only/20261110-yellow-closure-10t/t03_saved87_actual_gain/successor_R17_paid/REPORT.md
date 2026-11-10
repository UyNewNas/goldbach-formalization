# 第 84 项的整积分、矩形系数及计数

`P4AOriginalR17PaidIntegral.original_signed_density_and_count` 在同一个整数目标 N 上给出原 87 个第八层真六至八层收益积分 I87 的严格物理上界。令 `scale = singularSeries N / Real.log N`。上界 `integralUpper` 等于

```text
raw(orderedSixth, N, N, 0, z)
  − I87 * scale
  − p4aActualPresieveCorrection(keepEight, N, N, w, z)
  + (eta + u_c) * scale.
```

这里的 `keepEight` 是 T04 整个 R17 修订树的实际奇数读数。它与 R17 第八策略传给 `raw` 的读数定义相等。两个普通密度均在全部原模数上按 1/φ(d) 求和。小载体修正保留该第八树的全体有符号叶。严格不等式的左侧是 T04 给出的 `physicalDensitySum Q rho`，其中 `Q = moduli N w`，`rho = coefficient r n e q a omega N tau L`，标签取空，`tau` 取 `alignedWidth (data e q a).m k`。

## 同一组见证

先固定正 `eta`，用 R17 的 `original_ordinary_source` 选共同的 `r,n`，将两处分离的 `e` 上限取最小值、`q` 下限取最大值。对每个 `0<a≤1/100`，以及每组 `0<nu,v,u_c,betaMax`、`nu*v=19/96`，从 T04 的 `common_schedule` 一次取得 `beta,k,Nc`。它给出 `0<beta<min(1/8,betaMax)`、`beta²<v`、`omega=nu*beta²<a` 与 `nu*beta<1/1000`。将此 `omega` 代入支持所有 `omega≤a` 的普通增益式，取 `z=N^(19/96)`、`w=N^omega`、`L=N^(nu*beta)`，并把普通与编译的目标下限取最大值。

原增益式乘以严格正的 `scale`，给出 `(I87−eta)*scale < rawSix−rawEight`。T04 的同一矩形系数给出 `physicalDensitySum Q rho < rawEight−actualCorrection+u_c*scale`。两式合成上述整积分上界。量化及截断的原渐近损失由 `eta` 覆盖，正预筛与编译使用 T04 的一次 `u_c`。同参数另保留 T04 的四个原正项合计上界，其单独的 `eta` 没有进入整积分上界。

## 物理计数

在 T04 原本的 `b,T` 条件下，结论同时给出 `RealB` 关于实际 `card * physicalDensitySum Q rho` 的上界，以及将其中密度替换成 `integralUpper` 后的计数上界。`card` 是实际 `realHalfProductSource b N T` 的非负基数，两式均保留同一个 `realPhysicalDistributionError b N T Q rho` 以及 `ceil z + (T+1)`。共同收据还包含严格编译支出 `u_c * singularNormalization N` 和 `rho` 的严格模数支集界。分布误差仍是显式算术项。全局 PP 与其余 All22 账目的数值估计属后续职责。

## 安装与验证状态

两项直接 import 及所用定义和安装清单逐字节载于 `REGISTRY.json`。T05 四份同名 R17 源须成组安装，T04 基础有序第三层的公共 API 按既有补丁安装，T04 共程的已审 26 源按原清单复用。原 T03 四源及原积分、选中 archive、矩形程序与其支出沿用各自固定哈希。此处只新增一份 Lean 源。独立源码审查与远端内核核验是不同的证据，当前没有这个联合图的运行结果。本轮只读源码、原稿及指纹，没有执行原数值、有限守卫、Lean 或 CI。
