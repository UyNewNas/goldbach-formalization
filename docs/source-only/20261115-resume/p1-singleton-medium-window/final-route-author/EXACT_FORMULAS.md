# 精确对象、路线差别与下一真实输入

本文件是数学审查记录，不新增 Lean predicate、目标形前提或定理。所有未付估计都明确标为未付。

## 1. 原历史 saving 的完整公式

固定原 s,r,n,e,q,om 与 `H : FilteredSourceSupply s r n e q om`；H 原先对所有目标供给，n 等参数在 N 前固定。对实际 N,cap,w,z,L：

```text
R6_N = (sixthPolicy n e q om (N : ℝ)) false
R8_N = (policy (width r) n e q om (N : ℝ)) false
Δρ_N(d) = supported actual ρ(R6_N)(d) − supported actual ρ(R8_N)(d)
Π_N(d) = 1_[ floor(N^(9/20)) < d ∧ d < N^(599/1000) ]
E_N(d) = sharpPrimeError N d
savingMiddle = Σ_d Π_N(d) Δρ_N(d) E_N(d).
```

两个 retain-odd 输入的精确式也见 `P1OriginalOwnedGainSharpSupport:128–132`；此处指 `full87PhysicalRhoChange` 所绑定的原 sixth predecessor，绝不重定义策略。原完整 type 和零延拓在旧 `SOURCE_PINS.json` 所绑 `P4AOriginalFull87SignedSharpReceiver`；精确 middle 定义在已发表 `P1Original87SharpMiddleReserve:35–40`。

原 `beforeLeaves/afterLeaves` 与 owned state 按真实 occurrence list 取和；全部 tail primes、owner、mask、current sixth parent、finite eighth cap、小 β 和共同 N/cap/w/z/L 保留。原 f06293 支撑结论没有变成整盒 coefficient identity。

## 2. 原拟议 transfer 真正会留下什么

仅为审查该路线，考虑把上面的两个真实 retain policy 分别送进**现有** upper ALL/ANY compiler，使用共同实际 historical tag、同 fine width tau、同 small/rough carrier。记原 rough coefficient 为 λ_j，编译 coefficient 为 c_j，物理系数为 ρ_j、cρ_j，j=6,8。这一步没有供应这个 tag 的整盒几何，也没有断言它等于 final fallback 的常 tag 编译器。

令：

```text
Δρ_box = cρ_6 − cρ_8
η = (cρ_6 − ρ_6) − (cρ_8 − ρ_8) = Δρ_box − Δρ
B_mid = Σ_d Π_N(d) Δρ_box(d) E_N(d)
R_mid = Σ_d Π_N(d) η(d) E_N(d).
```

则有限代数恒等式是：

```text
savingMiddle = B_mid − R_mid.
```

这里 Π_N **必须保留**。将 B_mid 直接称为全 PP 又会多出完整模数 sharp filter 的分离问题，不能默默删掉。即便整盒因子已供应，付款还需 R_mid 的真正算术估计。这就是较强路线增加的输入；最终 compiled caller 并不要求这条恒等式用于付款。

对 rough carrier U 中的平方自由 b，令 χ_j(b) 是现有 compiler 的 `changed` indicator，且：

```text
β_b(a) = β⁺(a), if μ(b)=+1;
         β⁻(a), if μ(b)=−1.
```

由已有 `signAttachedValue_change` 和 cutoff-separated factorization uniqueness，对于实际 a∈small、b∈U：

```text
(cρ_j − ρ_j)(a*b) = χ_j(b) β_b(a)
η(a*b) = (χ_6(b) − χ_8(b)) β_b(a)
R_mid = Σ_(b∈U) (χ_6(b)−χ_8(b))
          Σ_(a∈small) Π_N(a*b) β_b(a) E_N(a*b).
```

β 的选择依据 **原 rough parity μ(b)**。不能改按 χ_6−χ_8、Δρ 或 η 的符号重选 β；例如 μ(b)=−1 且 only-after 时差的粗符号可能翻转，但原附着仍是 β⁻。已有源码已包含这个点值符号事实，本包不重新写它。

## 3. 已付 density 的精确强度，以及不能取的绝对值

已有 theorem：
`P4AUpperTaggedContinuationAccounting.physical_compiler_change_eq_signed_changed_masses:83–119`，其右边是：

```text
(Σ_a β⁺(a)/φ(a)) · M⁺_j
+ (Σ_a β⁻(a)/φ(a)) · M⁻_j,
M±_j = Σ_(b changed with that rough parity) 1/φ(b).
```

`ActualCompilerDensityReserve.exists_actualCompiledRho_target_density_difference_bound:151–168` 给原 nu,epsilon 的：

```text
|density(compiled) − density(raw)|
≤ [B/(nu*epsilon²)] · Σ_b |c(b)−λ(b)|/φ(b) · C_N/log N.
```

C_N 是原 `singularSeries N`。此处控制 |Σ β/φ|，不是 Σ |β|/φ。

若另有 |E_N(d)| ≤ C·N/(φ(d)log N) 且只在原 Π_N 支撑上使用，则从上节的精确公式最多先得到：

```text
|R_mid|
≤ C·N/log N · Σ_(b∈U) |χ_6(b)−χ_8(b)|/φ(b)
                    · Σ_(a∈small) |β_b(a)|/φ(a).
```

去掉 Π_N 只用于这个非负上界，不用于改写原系数。可用 χ_6+χ_8 继续放大，但没有消去 a 或尾部。

真正缺的是带 β 取消的算术 wall / AP 输入，而非再取一个 density 常数。不能把最后的绝对 β 质量用已付 signed density 代替；小筛因子不得删掉。两种实际 β(1)=1，故其绝对质量≥1。这个有限事实已由固定 provider 及实际 support 证明。它不证明 R_mid 很大，也不证明不存在更强带符号筛法估计；只阻止上述不合法替换。

`UpperCoefficientPerturbation.abs_signAttachedValue_sub_le` 的 M 同样只会是两个给定斜率的上界；当斜率改成每个 a 对应的 E_N(a*b)，旧 small-density supplier 的前提就不再是它。把已知 `physicalDensitySum` 界乘 N/log N 只给 mean-scale compiler 费用，不能凭归一化把它改成 signed error 界。

## 4. 终端实际可复用的对象

沿已发表 final rectangle schedule，冻结它已选择的

```text
m,r,n,e,q,a,nu,beta,k,kap,K,
omega = nu*beta² > 0,
ell = nu*beta,
P_N : Params = ⟨m,r,n,e,q,a,omega,k,N,ell⟩.
```

单一 beta 与单一 aligned k 在 N0 前；原历史 cutoff a 与物理 omega 不互换。原 κ/kap、K 亦先于目标阈值。对于其所有充分大偶 N：

```text
D_N = physicalDensitySum (Q omega N) P_N.rho
D_N < numericUpper m r n e q a omega eta uc N

|literal N (Q omega N) P_N.rho
  − primeMass N * D_N
  − singletonTensor P_N kap x U zeta|
≤ etaSharp * singularNormalization N

(singletonTensor P_N kap x U zeta : ℂ)
= singletonAtlas P_N kap K kap zeta.
```

这是已有 `original_single_prime` 的声明，不是待假设的新合同。其最终 `P_N.rho` 就是原 finite-fallback rectangle ρ；来自原 owned saving 的信息在 D_N 的 raw-density 比较中，不能把它说成 Δρ_N = P_N.rho。

本最终系数的 rough-prime enumeration cap 依源为 N；**singleton counted-prime enumeration cap 为 2N，physical target/residue 仍为 N**。这两个 cap 含义不得混淆。

设以下仅是既有表达式的数学缩写：

```text
L_N = P5CanonicalTentNarrowSingletonTransfer.actualLicence kap 6 N
S_N = P4BOriginalCollisionTensor.products P_N
c_N(d) = (P4BOriginalCollisionTensor.free P_N d : ℂ)

M_N =
  Σ js ∈ chartBank (2*N) 1,
    mediumAtlas L_N K (2*N) N kap
      (originalMediumLow zeta js) (originalMediumHigh zeta js)
      S_N c_N js.
```

这一个 M_N 是后续可挑的最小真实解析分支。应在原允许的正 zeta / sigma / kappa 范围中先作固定选择，然后对整个原 chart / group / interval / coprimality 家族给统一 N0、统一常数，并汇总其恢复标量。目标可取对任意 A 的 N/log^A N 界，再按原 H_N 规模吸收。不能因为 algebraic Atlas identity 对任意 zeta 成立即对任意 zeta 要求或声称估计。

31cce 已付 `roughPrimeReserve=0`。`singletonAtlas` 仍保留 trim、medium、noMedium、减 properPower 的原符号；已有 OneLong 支路不重复。付 M_N 不等于自动付其余项，更不等于付最终正双素数 count 的全部高秩 band。本包没有把这些尾项删掉，也没有引入任意 W 代替实际 singleton profile。

## 5. 分类与下一步的边界

| 项目 | 分类 | 本轮处理 |
| --- | --- | --- |
| 历史 Δρ 支撑、selected complement、原 owner/parent | 已有可靠工作 | f06293/8ac0 及旧真实源复用；不重做 |
| 由密度 compiler 推 raw sharp transfer | 额外路线缺口 | 精确指出缺的 R_mid 与 β 绝对值问题；不写此稿外更强 theorem |
| 原 saving 进入 final ρ 的 density 上界 | 已有实际接线 | 4733 的 unchanged_upper_sector/hjoined/hden 及 2ba 的最终 caller，精确复用 |
| final compiled ρ 的 singleton medium estimate | 原稿实质解析输入及实例族接线 | 本轮未取得供应；下一攻坚对象 |
| 是否原稿原命题为假 | 没有这样的证据 | 不作此结论 |

