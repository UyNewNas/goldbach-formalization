# Exact terminal boundary; no new premise is adopted

本文件记录仍待证明的实际结论，不添加 Lean axiom、目标形假设或等待该假设的 wrapper。

## Final singleton medium term

令 `P_N` 为既有 `P1OriginalSingletonRectangleSchedule.original_single_prime` 所用原 schedule 的 Params：原 `m,r,n,e,q,a,omega,k,N,ell` 完整保留，`omega=nu*beta²`、`ell=nu*beta`，共同 `beta,k` 在 N 前选定。这里不把任意抽象 Params family 冒充真实 87-history 族。

用原符号：

```text
L_N  := actualLicence kap 6 N
Q_N  := P4BOriginalCollisionTensor.products P_N
rho_N(d) := (P4BOriginalCollisionTensor.free P_N d : ℂ)

M_N := Σ js ∈ chartBank (2*N) 1,
  mediumAtlas L_N K (2*N) N kap0
    (originalMediumLow zeta js) (originalMediumHigh zeta js)
    Q_N rho_N js.
```

这就是原 `singletonAtlas` L 136 的 medium 子和；它不是 `RealB` 的两素数乘积 atlas。cap 是 `2*N`，剩余是 `N`，`K` 是 fixed before-HB rank bound，不能与 Params.k 的对齐深度混同。原首因子/剩余槽的 multiplicity、小 beta、符号、mask 与 owner 仍由 `products/free` 原定义产生。

最终实 receiver 需要这项的实部为 `o(singularNormalization N)`，与其他原符号支路一起付款。原 PP 路线给出的充分目标是：对每个固定 A>0，一个常数 C_A 和一个 N_A 先于目标 N 和所有随后允许的 chart/word/owner/history 标签，使

```text
‖M_N‖ ≤ C_A * N / (log N)^A
```

在原共同参数、原真实 family 与足够大偶数 N 上成立。本件没有证明这个目标。trim/noMedium/properPower/roughPrime 保持原 atlas 的加减号；旧 roughPrime exact zero 与 one-long 付款各保原范围。

## This candidate supplies exactly the original scale prerequisites

对任一选中位置 `i`，令 `C=owner(complement i n)`；原 `fibre bs i C` 按这个完整补积 owner 定义。选取 `i` 使用 `firstMedium` 的原位置顺序，在读 n、模数或误差符号前固定。一个实际非零 `integerProfile kap 6 N cj kap0` 产生完整 fibre 的尺度：

```text
p := completeProduct n
U := lower (bs i), V := lower C, x := U*V, X := R cj
N^(1-kap0) < p ≤ 2*N
x ≤ p ≤ 4*x
X/2 < p < 2*X
X^(3*zeta) ≤ U ≤ X^(1/3+zeta/4).
```

因此统一地得到 `x/2≤N≤x^(1+kappa)`、`x^(2*zeta)≤U≤x^(1/3+zeta/2)`、`2U≤x` 和 `x≤v≤x²`，其中实际 `v=2^(6*K+3)*X`，原 `Zchart=roughF v` 不变。

原 `Part3.ActualRoughIntervalAllModuliSW20261028.exists_original_chart_rough_AP_all_moduli` 的几何参数现在可取本 x、v、theta=2*zeta。其已有常数顺序是固定 A,L,theta 后 C,x0，再对 x,v、所有辅助 k/q/reduced residue、useMu、频率及个别区间统一。将 xMin 取它的 x0 后，本 candidate 给出物理 N 阈值；区间 `U≤lo≤hi≤2U` 自动满足 `hi≤x`。

这只是几何对接。源级完整的 singleton 角色、实 Möbius 截断/归一化 log、原 retained band 及所有 restoring factors 尚未由本文件构造。已有 P4B generic `alpha_one/alpha_rough/restores` 与原 rough-SW 分析可以复用，但 P4B 的两组 family Index 不可以替换成本 actual singleton；不把两组 log^54 budget 直接搬过来。

## The remaining signed M estimate

真实局部 atom 应保持原目标 N 为 residue，alpha 为该实际选中 HB 槽，beta 为同 fibre 的其余有序槽卷积，三个 gamma 为同一最终 free 系数在整个 box 上固定分组的 one-bounded 因子。原 signed sum 是：

```text
Σ q1 ∈ factorCarrier Q1, Σ q2 ∈ factorCarrier Q2,
  Σ q3 ∈ factorCarrier Q3,
    gamma1(q1)*gamma2(q2)*gamma3(q3) *
      Σ u ∈ alphaCarrier, Σ v ∈ betaCarrier,
        alpha(u)*beta(v) *
        (1_(u*v ≡ N mod q1*q2*q3)
         − 1_((u*v,q1*q2*q3)=1)/phi(q1*q2*q3)).
```

只有最外面取范数，不能改为模数逐项绝对值。全部 alpha 区间/系数、beta、gamma 在模数求和前固定。beta 的 divisor order 固定于实际有限 HB 槽和原归一化，不随所求 A 增长；alpha 的辅助 SW 常数先于整族的 atom、k、q 和 residue。

原 `MediumAdmissible B sigma kappa c0` 还要求四条：

```text
Q1 < U*x^(-sigma)
U²*Q2*Q3² < x^(1-8*sigma)
N^(7/32)*U*Q1*Q2^5*Q3² < x^(2-15*sigma)
U^(1+2*(7/32))*Q1*Q2^(5-2*(7/32))*Q3^(2+2*(7/32))
  < x^(2-15*sigma).
```

并有 `0<sigma<1/100`、`0<kappa≤sigma/100`、`c0*x≤N≤x^(1+kappa)`、同 alpha 的 roughness 与全部 auxiliary SW，以及原 exact coprime mean。此 leaf 只付其中尺度/rough-cutoff 的必要条件，不供应 whole-box 三因子 licence，也不供应 uniform signed arithmetic conclusion。不存在把 `RestrictedMediumObligation` 定义本身当证明的步骤。

## Existing half-J and its precise remaining application boundary

已审 endpoint：
`OriginalNativeJFromPrimeWeil20261115.original_range`，dca6bab3 的 source-only archive，SHA `09057444af3e88b94b225a3b0966b53ff249e2f8edf18c3e1d6059a5fef57d35`。

```text
∀ epsilon>0, ∀ fixed A≥0, ∃ C>0,
∀ S,j,Q,X,omega, Q>0 → X>0 → S⊆classicalLevels Q →
 X≤A*max(M_j,Q²/M_j) →
 pascadiJ S X j omega
 ≤ C*((1+Q)*(1+M_j))^epsilon*(Q+M_j)*M_j.
```

它无需 hJ/hHalf/hWeil 参数，保留同 positive-m interval/common phase；四 mother 尺度各自缩放旧 critical 输入。数学 AL 为 `c2611ba9133c8b331efd0cbff30c5c310d2cda186c2c464fef416af0a234aa47`，其 source-only/未 kernel 状态不变。本 candidate 不导入、重证或削弱此 endpoint。

在 medium 原文 L 349–380，需要真实 Poisson/Kuznetsov packet 的共同 m 区间和相位、原 n 系数以及固定尺度归一化；L 382–416 再回到原 N,Q,R,S,M、保留零 Poisson 项、nu 权和两次开方。J 只支付其中原适用范围内的谱平均输入；还须证明实际所用 S,j,Q,X 落入该范围，且 A 在整族前固定。这里不能为每个 N 或每个后选标签重新挑一个增长的 A，再援引统一 C。

本件未审定其他全谱输入、普通/异常返回与真实 signed M 全连接；没有据此作“原稿有反例”的结论。下一次推进应保留这条具体分析边界，而非再加 desiredAtlas 或 raw-to-boxed 强接口。

