# 实际 singleton 短系数质量与 Brun 前因子

**SOURCE ONLY：未 elaboration、未编译、未核验 kernel，formal credit = 0。** 本目录只含两个新有限估计候选及来源记录；没有修改仓库、既有源、执行入口或验收身份。

新 owner 是 [P1OriginalSingletonShortMass.lean](P1OriginalSingletonShortMass.lean)。它只 import 已发布 H 的 `P1OriginalSingletonFixedScaleTransport`，调用现有 `shortSequence_mass`，补上 H 后尚未接入的实际 singleton 系数实例。

## 两条候选声明

记 `X0 = shortScale bs`，仍是**全部原 block lower 的乘积**。短位仍为 `ShortPositions i k`，并使用原 `shortSupport`。短系数逐项保持原 Dictionary 中的

```lean
shortSequence (fun a : ShortPositions i k => bs a.val)
  (beforeHBCutoff K [cj]) (fun _ => hbCutoff cj)
  (fun a => xi a.val) (fun a => rowRoles j a.val) m
```

没有新定义系数或替换 carrier。原有序元组碰撞、符号、unit、重复位置、Möbius 截断、分子对数和 Mellin 相位均留在这一旧对象内。

`eventually_actual_singleton_short_mass` 的结论为

\[
\sum_{m\in\mathrm{shortSupport}}\lVert\alpha_m\rVert
\le X_0^{40\zeta}(1+\log X_0)^4.
\]

原 `shortSequence_mass` 已给出 `M * (1+log X0)^s`，其中 `M` 是原短位 lower 乘积、`s` 是短位数。它使用精确 `shortRectangle.card = M`，没有额外的 `2^s` 因子。本候选直接用 H 的实际 `M ≤ X0^(40*zeta)` 和各短块 `2*lower ≤ X0` 支付其前提；`short_card` 与 `j ∈ range 3` 给出 `s ≤ 4`，再用 `X0 > 1` 比较对数幂。

`eventually_actual_singleton_brun_short_mass` 继续取同一原 cutoff

\[
Z=\mathrm{beforeHBCutoff}(K,[cj]),\qquad
Y=Z^{2\mathrm{halfOrder}(X_0)+1},
\]

给出

\[
Y^2\sum_{m\in\mathrm{shortSupport}}\lVert\alpha_m\rVert
\le X_0^{40\zeta+2\varepsilon}(1+\log X_0)^4.
\]

这里直接复用 H 对实际 `Z`、实际 `halfOrder X0` 给出的 `Y ≤ X0^eps`，只作非负平方与实数幂乘法。它没有重新证明 Brun 支撑、factorial 密度或幂到对数的支付。

## 实际前提和量词

两条声明都使用 H 已有的 `kappa > 0`、`kappa ≤ zeta/10000`、`zeta ≤ 1/400` 和 `kap0 < kappa/(4*(1+kappa))`。固定 `K` 后才取物理 `N` 阈值；第二条另在阈值前固定任意正 `eps`。第一条调用 H 时内部取 `eps = 1`，仅利用其实际短积和短块结论。

阈值之后统一量化 `kap < 1`、`B,cj,j,bs,ns,i,k`，以及任意实数 Mellin 频率 `xi`。使用的实际几何前提只有原 `j ∈ range 3`、两位置不同、原 rectangle 中的一个 tuple、同一完整乘积上 `scalarProfile ≠ 0`，以及 Dictionary 已提供的每个剩余短位 lower 小于 `originalMediumLow zeta [cj]`。

没有 aggregate coefficient 非零、整 rectangle 活跃或最终误差估计的假设。`Q,rho` 不参与这些系数质量估计；现有 same-Q/rho Dictionary 及其精确 coprime mean 完全不变。

## 来源与本轮边界

固定手稿为 `UyNewNas/chen-imbalanced-semiprimes@a988cba584d803ae2856a0de50efb582f4f3dd6a` 的 `paper/release-20261106/en/coefficient-appendix.tex`。535–548 行保留原完整乘积与 rough 投影；621–630 行给出两长及短补集；765–820 行的正 gap 比较仅在取绝对值时使用短系数模，其总预算包含 `M*y^2` 和 `M*y^2*D^(3/2)`。本候选完成这里的实际短质量和 `y^2` 前因子实例，属于可补齐的有限装配。

[SOURCE_REVIEW.json](SOURCE_REVIEW.json) 记录六个有界读取的项目来源、精确字节指纹、H commit `f6fdd7fffe17803c60914bf28b39b55715d34464` 一致性，以及当前匹配 Mathlib API。现有 historical P2 invoice 仍使用通用 `hX/hcap` 接口，未提供本实际 singleton 固定尺度实例；旧 generic 质量证明没有复制。另一代理正在复用原 generic 幂到对数支付，本目录不重复该步骤。

根代理已独立静态核对两条声明、原 supplier 签名、carrier/role/cutoff 身份、量词、And 投影及实数幂平方，未发现具体阻断。该审查不是 elaboration 或 kernel 验收。

当前仍继承 H 的 source-only 与源闭包边界，没有重新搜索或重建已登记缺源。本目录不声称 rough-to-upper 精确均值装配、P2 核心、sharp strips、Fourier 重构及 L1 tail、外层 Atlas 预算已经完成，也不声称完整 P1.5 已验收。
