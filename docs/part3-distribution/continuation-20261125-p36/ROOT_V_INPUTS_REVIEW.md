# 原 U5 RootV 输入供应者：独立源码审查

日期：2026-11-25。审查对象为冻结候选 [P3OriginalU5RootVInputs.lean](../../source-only/20261125-p36-root-v-inputs/ImbalancedChen/P3OriginalU5RootVInputs.lean)，SHA-256 `76fe9772dc83d81d617a13c980cfc0de828d33948c030e5cfe15f61d84d77f73`；同时核对其 README、FREEZE、公开声明表及 [NEXT_F_CONSUMER_REVIEW.md](NEXT_F_CONSUMER_REVIEW.md)。

**结论：在明确的局部尺度域及真实最后来源为 root 的范围内，未发现已确认的数学缺陷、把待证临界区间当作假设、换用系数或扩大来源范围。该文件确实供应点态 RootV 的数值输入；尚未供应 whole-atom 或完整 physical-family 的 (F)。本次只读源码并写此报告，未运行 Lean、kernel replay 或公理审计。**

## 1. 实际 root 路由

已对照原 `P2OriginalSelectedPairNativeData.rootLevel` 与 `Part5OriginalUpsilon5CausalDictionary.level`：`false` 分支确为 `max(v(t), max(v(t+u), B(a)))`，其中 `t=coordinate N t.2`、`u=coordinate N t.1`。

| `rootRoute` 输出 | 实际选择 | 充分性 |
| --- | --- | --- |
| `some false` | 原较大素数 `[t.2]` | 条件同时给出 `v(t+u)≤v(t)` 和 `B(a)≤v(t)`。 |
| `some true` | 原初始二素数 `[t.2,t.1]` | `B(a)≤v(t+u)` 与第一分支未触发，推出 `v(t)≤v(t+u)`。 |
| `none` | 原 `B(a)` 值 | 两个 V 值均不大于 `B(a)`；只返回 W 路由和值，没有声称 W 分配已完成。 |

相等时先 singleton、再 pair 的规则只选取已达到原最大值的分支。新 (F) prefix 没有被等同于 all-source 的两外标 S-mask；原 policy、source、mask 都由原 `SignedSupply` 保留。

## 2. 换底与完整临界区间

`q=log N/log x` 的 `1≤q≤1+κ` 是从明确输入 `1<x≤N≤x^(1+κ)` 推出。旧 `physical_power_eq_local` 的方向使用正确：`N^ell=x^(q*ell)`，于是 `D=x^(theta_cov−2ζ)=N^ell`；所选乘积同样满足 `x^(q*s_I)=prefix.prod`。这里 `ell=rootLevel−b`，没有换成 `.599` 或原 physical Q。

`v_rescale_lower` 也成立。旧 `v_eq_min` 给出 `v=min(A,C)`，`A(s)=(1+s)/2`、`C(s)=57/64−3s/2`；换底只损失截距 `(q−1)/2` 或 `57(q−1)/64`，两者均不超过 `κ`。这证明 `q*v(s)−κ≤v(q*s)`，不要求额外的 `s` 符号假设。

在实际 V winner 上，`q*b≥b` 且 `κ+2ζ+b/4≤3b/4≤b`，因此原 buffer 给出 `theta_cov+b/4≤v(q*s_I)`。调用旧 `actualSelectedSubproductV_residue_margin` 的参数正是 `e=b`、同一个 `κ`、`theta=theta_cov`，得到 `b/8` 余量。再由旧 `actualSelectedSubproduct_critical_iff` 得到完整区间

\[
2\theta_{\rm cov}-1\le q s_I\le
\min\{(32-39\theta_{\rm cov})/34,
(2-2\theta_{\rm cov}-7(1+3\kappa)/32)/3\}.
\]

两个上界均保留；只在未扰动的 `v` 中使用两项化简。`alpha0=1+3κ≥q`、`1/2<ell<153/256` 亦由本地输入推出。最终 `zeta_pos` 字段保留 `0<ζ`，没有把它作为无用途的域声明。

## 3. 完整词、complement 与非零 rho 入口

从 `.root` 的 `SignedSupply.full` 取出的 cap 按定义恰为 `rootLevel−b`。`integerSquareGates_at` 转成相同完整词的 `actualDwellSupport D`；`factor_words` 只把该词拆成 singleton/pair 初始 prefix 与剩余词，没有删除 `chosen` 或 `s.primeFactorsList.reverse`。prefix 正性来自原 pair 的素性。

旧 `actualDwell_selected_prefix_budget` 的真实结论恰是 `actualDwellSupport (D/prefix.prod) remainder`，所以此处 complement 的每个后续平方保有原 preceding product；无需新的初始门槛，也没有从无关 mask 的 selected squares 迁移结论。`canonical` 保持与 `(fullModulus t k).primeFactorsList.reverse` 的精确等式。

`native_U5_root_V_inputs` 首先消费原非零 `rho N epsilon (selectedPolicy ... false N t) k`，返回原 `s/chosen/source/slots`、乘积、accepted trace 和整个 `SignedSupply`（含 `same_rho`）。新增断言在返回值中是 `source=.root → ...`；没有把 fresh-row 改名为 root，也没有声称所有非零系数都属于 V 分支。`signed_root_V_inputs` 的上游 `SignedSupply` 是已明确的全词供应接口，待证 winner、critical interval 和新 prefix remainder budget 均不是输入。

## 4. 稿件对应及尚未关闭范围

已核对固定 [20261106 coefficient appendix](https://github.com/UyNewNas/chen-imbalanced-semiprimes/blob/3ffa2d159c9974e2ca6d5f930c0f2c16baa0135e/paper/release-20261106/en/coefficient-appendix.tex)（blob `10f3e2efb2074a9b97148a5151956e1d450be13f`）的 compact rescaling、Three-factor representations 与 signed beta attachment 段。候选的 base-x 换底、`alpha0≥q`、两上界和 full/selected squares 的层级与稿内公式一致。

实际 medium charts 的 `x≤N` 及统一 `κ,ζ` 仍需供应；一般 `c₀x≤N` 不能直接替代它。`rootRoute` 目前依赖实际点，未给整个 coarse box 的共同路线、端点 reserve 或固定 slot partition。W、fresh-row (F)、medium A 的 C≥1/C<1 接线、共同 physical Q 与全族 exact factorization 也未由本文件完成。这些是明确的后继供应范围，不是本定理内部的反例。

small-beta 的完整素因子词虽参与点态 full/complement support，但没有被塞进固定 rough rank `J`；源码和 README 都保留独立 `s`。后续应继续按稿件把整个 sign-selected beta 附到一个组，不能以该 canonical 全词直接申请统一正指数下界或固定 rough-rank 长度。已验收的 P3.5 whole-height 工作不在本次重审范围内。

**验收状态保持 source-only。** 本审查不赋予该候选或其尚未验收前置新的编译、kernel 或数学闭合信用；没有修改作者 Lean 文件、main manifest 或编译安排。
