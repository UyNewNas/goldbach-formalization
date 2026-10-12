# Part 3：算术分布与实际误差供应者交接

## 结论与验证状态

本 Part 已写出有完整证明体的 Lean 候选：真实素数 BV 的共同区间／变化余数接口、当前四个下界素数带的 AP 误差池，以及一个长整数因子的实际同余分布与归一化。高物理模数的 restricted signed factorized distribution 仍未闭合，实际完整上／下 policy 的误差供应者也未闭合。

**目前没有成功执行新文件的 Lean elaboration、kernel replay 或传递公理检查。候选代码不能登记成已核验定理。** 本地原版 Lean 在读取参数前退出；独立 CI 配置用于正常验证全部五个新模块。执行证据单独记在本目录，不能把静态扫描或 workflow 的存在当作证明验证。

本次没有把主线改为弱 Pan/Selberg，也没有修改共享根导入、原有证明文件、依赖、手稿地图或其他 Part 的文件。

## 1. 固定来源

| 对象 | 完整固定版本 |
|---|---|
| 形式化基线 | `1a80c1bcce67886f699d097fc37fd245cd3620bf` |
| 基线 Git tree | `1fd54b8b4d5fd89abc767ee7e8d814453453b29c` |
| 来源分支 | `codex/variable-envelope-boxes`；内容以基线 SHA 为准 |
| 本 Part 分支 | `chatgpt/chen-p3-distribution` |
| 手稿 | `UyNewNas/chen-imbalanced-semiprimes@ba6ec11d800eccc54406490631895e174de85766` |
| 主文 blob | `d529bea2ecfcc74d64fc1664ac770a3becaa7c79` |
| Lean | `leanprover/lean4:v4.33.0-rc1` |
| Mathlib | `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1` |
| goldbach-lean | `09b97db5764ade1246bfb77206baa1b124760958` |

手稿版本取自基线的 [CURRENT_MANUSCRIPT_MAP.md](../CURRENT_MANUSCRIPT_MAP.md)。当前常数是 `K = 8452171/1250000`，不是历史草稿的数值。

手稿固定文件：

- [主文](https://github.com/UyNewNas/chen-imbalanced-semiprimes/blob/ba6ec11d800eccc54406490631895e174de85766/paper/source/manuscript-body.tex)：`prop:current-medium`、`eq:current-aux-sw`、`eq:current-medium-conclusion`、`eq:current-PP`。
- [medium 补全](https://github.com/UyNewNas/chen-imbalanced-semiprimes/blob/ba6ec11d800eccc54406490631895e174de85766/paper/source/modules/distribution-medium-completion-20261010.txt)，blob `19f9672bc9b6d455045213c5e23e10433a9569d2`。
- [prime-product 补全](https://github.com/UyNewNas/chen-imbalanced-semiprimes/blob/ba6ec11d800eccc54406490631895e174de85766/paper/source/modules/distribution-prime-product-completion-20261010.txt)，blob `5e59d2881181b29446e5786584d6442e7a96fe04`。
- [coefficient 补全](https://github.com/UyNewNas/chen-imbalanced-semiprimes/blob/ba6ec11d800eccc54406490631895e174de85766/paper/source/modules/distribution-coefficient-completion-20261010.txt)，blob `7f5b9685455440149976c28afef10c102305589f`。
- [经典输入对应表](https://github.com/UyNewNas/chen-imbalanced-semiprimes/blob/ba6ec11d800eccc54406490631895e174de85766/paper/source/modules/final-classical-input-correspondence-20261010.txt)，blob `df2070a5114dc1d8727a9c5853947a2e03659ccc`。

## 2. 真正需要的类型与已有供应者的差异

| 供应者／现有文件 | 实际提供什么 | 当前主线还缺什么 |
|---|---|---|
| `AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418.standardBombieriVinogradov` | 真实素数 AP，真实 `li` 主项；共同外端点的所有前缀、所有原始余数的最大误差；物理 `q ≤ floor(N^(1/2)/log(N)^B)`；一个统一阈值 | `.599` 物理范围、素数乘积源、divisor-bounded medium 槽、谱返回的共同非零相位 |
| `liuMainPanCoprimeIntervalMaxL_boundedAggregate_log_saving` | `a*p ≤ N` 中 `p` 真素数，`A₁<a≤A₂≤N^(2/3)`，`log(N)^(2B)≤A₁`，实一有界 `f(a)`；内层 `a` 的抵消保留；逐物理模数取绝对值；统一 `C,B,N₀` | 物理范围仍是平方根；不能吸收依赖 `a*p` 的任意相位；不供应当前全部编译系数或高模数 signed 估计 |
| `RestrictedResidueScale` | 对完整局部尺度 `c*N^(1-κ₀)≤x≤C*N`，统一得到 `C⁻¹*x≤N≤x^(1+κ)` | 本身不含分布估计；`x` 不能偷换为剩余商 |
| `HalfProductPanFinite` | 真正半乘积源按较小素数分纤维，保留平方对角线与计数重数 | 有限重排不提供误差渐近 |
| `PanProductLiuBridge` | 真正乘积前缀／区间与 Pan API 的精确对应，原始余数归约 | 每个端点仍须满足以该端点为尺度的 Pan 门槛 |
| `ChenPooledQuotientAP` | 完整模数 `b(t)*e` 的注入池化；保留次级 AP 误差、中心修正，无 selector-cardinality 损失 | 它是有限不等式；须另给该完整物理模数范围内的分布供应者 |

`trueLogarithmicIntegral x` 在 pin 中是 `2/log 2 + ∫₂ˣ dt/log t`。本 Part 的真实素数适配器没有改成 `x/log x`，也没有把 primitive-coprime 主项改成未经互素过滤的总质量。

当前 coefficient 补全区分 carrier `299/500` 与辅助分解许可。共同膨胀后使用 `theta_* = 599/1000`，并需 `theta_*/(1-κ₀)<3/5`。低秩所列 `19/48`、`38/125`、`1527/3584` 有固定平方根间隙；仍需 Part 1 对实际支持完成膨胀、尺度转换和端点证明。

弱 Pan/Selberg 路线只在 `θ<(1-κ₀)/2` 供应局部物理模数，其 Selberg 系数 `4/θ>8`，不能供应当前 `K=8452171/1250000`。把 `sqrt(N)` 直接用于 `Y≈N^(1-κ₀)` 会丢掉 `N^(κ₀/2)` 的幂量级，不能用对数裕量支付。

## 3. 未闭合 medium 目标：量词、范围与相位

[Part3DistributionTargets.lean](../../ImbalancedChen/Part3DistributionTargets.lean) 定义了 `ImbalancedChen.Part3.RestrictedMediumObligation`；这是待证的 `Prop`，没有声明其证明，更没有作为公理加入。

对一个预先固定的 family `F : ι → MediumAtom`，每个成员的数据是完整尺度 `x=U*V`、可变化整数余数 `a`、一个共同 `alpha` 区间、系数 `alpha,beta` 和三个独立的 `gamma_i`。估计的原式为

\[
\left|\sum_{q_1,q_2,q_3}\gamma_1(q_1)\gamma_2(q_2)\gamma_3(q_3)
\sum_{n,m}\alpha_n\beta_m
\left(1_{nm\equiv a\ (q_1q_2q_3)}-
\frac{1_{(nm,q_1q_2q_3)=1}}{\varphi(q_1q_2q_3)}\right)\right|.
\]

所有 `gamma` 的符号都在最后的范数以内。物理模数是 `q1*q2*q3`；三个 `Qi` 是分开的辅助因子长度。代码用 `ceil(Qi)≤qi≤floor(2Qi)`，容纳 `Qi=1,qi=1`。这只是对手稿 `qi≈Qi` 的具体端点约定；Part 1 必须证明其 atom 划分对重合端点的唯一归属或确切重数。

固定 `ϑ=7/32`，必须同时有

\[
\begin{gathered}
c_0x\le |a|\le x^{1+\kappa},\qquad Q_1<Ux^{-\sigma},\\
U^2Q_2Q_3^2<x^{1-8\sigma},\\
|a|^{7/32}UQ_1Q_2^5Q_3^2<x^{2-15\sigma},\\
U^{23/16}Q_1Q_2^{73/16}Q_3^{39/16}<x^{2-15\sigma}.
\end{gathered}
\]

系数类保持原限制：`alpha` 一有界、一个区间、`P⁻(n)>x^(1/(log log x)^3)`；`beta` 有一个固定 divisor order；每个 `gamma_i` 一有界且非零时 `(qi,a)=1`。粗糙支撑本身不推出辅助 SW。`UniformAuxiliarySW` 要求先取 `C_A,x₀`，再统一于全部 family 成员、区间、`k,q,b`，且保留 `τ(k)^C0`。

完整目标次序为

```lean
RestrictedMediumObligation F B C0 σ κ c0 :=
  0 < σ → σ < 1 / 100 → 0 < c0 → 0 ≤ κ → κ ≤ σ / 100 →
  (∀ i, MediumAdmissible B σ κ c0 (F i)) →
  UniformAuxiliarySW F C0 → RestrictedMediumTarget F

RestrictedMediumTarget F :=
  ∀ A : ℝ, 0 < A → ∃ C : ℝ, 0 < C ∧ ∃ x0 : ℝ, 1 < x0 ∧
    ∀ i, x0 ≤ (F i).scale →
      ‖(F i).signedError‖ ≤ C * (F i).scale / (Real.log (F i).scale) ^ A
```

这允许 family 无限，但它的 SW 常数和目标阈值必须统一。`∀ i, ∃ x0_i` 不是此类型的供应者。

谱证明中的共同区间与共同加性相位另由 `CommonCompletedVariable` 表示；其字段没有 level 索引。`CoprimePacket.transformedCoefficient` 保留

\[
1_{(n,a)=1}\,\beta(\nu n,z)e(-n/z),\qquad (a,z)=1,
\]

没有 spectral-height 参数。这两个结构只固定合法数据，**没有证明谱大筛、packet 二次型、Kuznetsov 或 dispersion estimate**。普通 BV 的零相位接口不能替代这个输入。

## 4. 真实素数 BV 与当前下界低秩带

[Part3PrimeAPDistribution.lean](../../ImbalancedChen/Part3PrimeAPDistribution.lean) 首先把 `chenPrimeAPCount Y a d` 与 pinned 真实 `primesInAP Y d a` 逐项对应，再用真实 BV 的 prefix maximum。对任意 `A>0`，先选择 `B,C,N₀`，然后统一于

- 所有 `N≥N₀`；
- 所有 `Q≤floor(N^(1/2)/log(N)^B)` 与任意子支持 `S⊆[1,Q]`；
- 所有共同端点 `L≤U≤N`；
- 所有变化余数选择 `a(d)`，只要求 `(a(d),d)=1`；
- 所有实带符号权 `|w(d)|≤1`。

估计 `Σ_d w(d) E(L,U;a(d),d)` 的绝对值不超过 `2*C*N/log(N)^A`，其中

\[
E(L,U;a,d)=\#\{L<p\le U:p\equiv a\pmod d\}
-\frac{\operatorname{li}(U)-\operatorname{li}(L)}{\varphi(d)}.
\]

乘数 `2` 来自两个实际端点。没有附加“此误差已趋于零”的假设；分析输入是 pinned 中已有完整证明体的 `standardBombieriVinogradov`。新适配器本身仍待编译。

[Part3CurrentLowerDistribution.lean](../../ImbalancedChen/Part3CurrentLowerDistribution.lean) 用当前 `a=417/5000,h=19/125,d=59/250`，没有误用历史 `chenUpsilon36` 的旧参数。四行选择器是：

| 行 | 当前素数带 | BV 门槛作用于 |
|---|---|---|
| Y3 | `N^a≤p<N^(1/3)` | `p*e` |
| Y4 | `N^a≤p<N^d` | `p*e` |
| Y5 | `N^a≤p1<p2<N^h` | `p1*p2*e` |
| Y6 | `N^a≤p1<N^h≤p2<N^d` | `p1*p2*e` |

`Part3CurrentLowerRows` 保留实际 sieve-product 除子条件和完整物理模数上界。四个误差和用因子 `4` 汇入同一个 primitive AP 池；没有按素数选择器基数乘大误差。

最后的 `part3_quotientRemainder_log_saving_add_centre` 控制的是实际 `BoundingSieve.rem`。它保留

\[
\bigl[1+4(1+\log\max(1,Q))\bigr] C N(\log N)^{-A}
+\operatorname{chenSelectedCentreCost}.
\]

不能把这个结论读成“全部归一化余项已付清”：要用更高 logarithmic accuracy 支付显式对数损失，还须用实际中心修正估计，并由 Part 1 证明编译出的每行满足这里的完整模数条件。该文件没有声称实际完整 lower policy 已实例化。

## 5. 独立的长整数因子分布

[Part3LongSlotDistribution.lean](../../ImbalancedChen/Part3LongSlotDistribution.lean) 的对象是实际整数积 `m*n`，长变量在同一个 `[L,U)`，不是素数质量极限或筛的恒等式。令

\[
R_{q,a}(m)=\#\{L\le n<U:mn\equiv a\pmod q\}
-\frac{\#\{L\le n<U:(mn,q)=1\}}{\varphi(q)}.
\]

对 `q>0,(a,q)=1`，候选证明给出 `|R_{q,a}(m)|≤2`，统一于全部 `m,L,U,a`。证明把每个前缀的余数计数写成整商加一个指示量，再支付两个端点；互素主项是原始余数计数的精确平均。若 `(m,q)>1`，两个实际计数同时为零；若 `(m,q)=1`，用模逆回到一个余数类。

随后对任意复数系数有

\[
\left|\sum_{q\in Q}\rho_q\sum_{m\in S}\alpha_mR_{q,a}(m)\right|
\le 2\left(\sum_{m\in S}|\alpha_m|\right)
       \left(\sum_{q\in Q}|\rho_q|\right).
\]

对 `m≤M,q≤D` 的一有界系数得到 `2*M*D`。这里在先取得足够小的真实逐模数误差之后才用三角不等式；它不承担 medium 分支所需的高模数带符号抵消。

[Part3LongSlotNormalization.lean](../../ImbalancedChen/Part3LongSlotNormalization.lean) 使用基线已有幂量级支付对数误差的定理：固定 `theta<1` 后，先取同一个阈值，再让全部 `M,D,L,U,a,alpha,rho` 变化；只要求实际 `M*D≤N^theta`，则误差小于任意 `epsilon*N/log(N)^K`，也小于任意 `epsilon*singularNormalization N`。

该结果服务 prime-product 补全第 7 节的 one-long 分支：`M≤x^(20*zeta)`、`D≤x^Theta_loc` 和 `20*zeta+Theta_loc<1` 给出所需幂间隙。但长槽目前是无粗糙筛选、系数为一的整数槽。Brun projector、smooth/Mellin 变化成本与两长槽 Weil 分支未接入；不能把本结果宣传为对任意长槽相位、粗糙数或素数已成立。

这一相位限制有具体检验：若擅自给长槽加上 `e(n/3)`，取 `q=3,m=a=1,[L,U)=[0,3H)`，则加权 AP 数为 `H*e(1/3)`，加权互素质量为 `-H`，误差为 `i*sqrt(3)*H/2`。因此常数 `2` 不能原样推广到任意共同加性相位。这说明本 Part 的 elementary lemma 不能替代谱返回；它不是对手稿当前谱估计的反例。

## 6. 文献核对的结果与尚未证明的步骤

重新核对的原始来源是 [Pascadi v3](https://arxiv.org/html/2404.04239v3)、[Assing–Blomer–Li v1](https://arxiv.org/html/2005.13915v1) 与 [Drappeau 作者版](https://drappeau.perso.math.cnrs.fr/documents/divtm-siegel.pdf)。Pascadi Theorem J 是共同相位的 level average；不能直接允许各 level 自选相位／区间。ABL Lemmas 3.1–3.2 有互素前提及 transformed coefficient 的二次型结构；有限 coprime specialization 不等于抹去 packet 内部权重。

本次审查未建立针对**当前 restricted 版本**的具体反例，也未发现可确定宣告为错误的引用接口。旧版本的 unrestricted 扩张不作为本次靶标。以下是准确的未完成证明位置，不是已证明其错误：

- medium 补全的 (18)、(23)、(24)：从保留主 Gram 方差、完整互素分拆、retained phase 和 packet 二次型到实际算术 dispersion estimate 的推导，尚未在 Lean 供应者中找到，也未独立重建完毕。
- (21) 的 reciprocity 必须保留最后相位；其五坐标变化损失是 `x^(5*kappa+o(1))`，不能改称任意 `x^epsilon`。代码未声称已供应这一步。
- (24) 到 (25) 的代数比较、最终指数预算可以核对，但这些比较不证明其输入 (24)。以 `kappa≤sigma/100` 支付负指数间隙，也不能替代谱估计。
- 从 medium、一长槽、两长槽和低秩 BV 拼装到 `eq:current-PP`，仍须为实际几何 family 支付共同 smooth/Mellin、Brun 和有限分拆成本。

## 7. 实际上／下源的最小剩余输入与接收 Part

`primeProductSignedError` 已把有限 labelled 真素数元组写成实际同余误差，保留重复素数及 slot 次序。`UniformPrimeProductTarget` 的完整原式在目标文件及 [定理类型清单](THEOREM_TYPES.md) 中。

这个类型目前是**误差结论**；不授权任意函数 `W` 作为手稿的几何权。要形成实际供应者，至少还要完成以下连接，不能在一个叫 `Admissible` 的未展开假设里藏入所求误差估计。

| 未闭合输入 | 精确工作 | 接收／负责衔接 |
|---|---|---|
| 实际有限 policy 数据与恒等式 | Part 1 构造上下／marked／switched 物理 `rho_N`，证明 actual source 等于这些 labelled prime-product 权的组合，保留重数、目标删除、实际物理 cap 与有限 atom 的端点归属 | Part 1 → Part 3；Part 0 跟踪 |
| 几何合法类 | 固定 `a_*>0`、rank、正下界 `p_i≥c*N^a_*`、完整乘积 `O(N)`、仅几何 gates、共同 polylog Euler-derivative bounds；每个 high-rank box 有整个 box 上的独立三因子分解许可 | Part 1 → Part 3 |
| restricted medium theorem | 证明上文完整 `RestrictedMediumObligation`，包括统一辅助 SW 的实际 rough `1`/Möbius 槽和谱返回；不是新增公理 | Part 3 → Parts 4/5 |
| prime-product 组装 | 把低秩 BV、rough/smooth one-long、two-long 与 medium 分支接到同一个 `UniformPrimeProductTarget`，阈值覆盖全部实际 family | Part 3 → Parts 4/5 |
| 当前 lower 的合法低秩实例 | 实际 Y3–Y6 支持满足完整 `p*e`／`p1*p2*e` BV cap；支付次级对数损失和 centre cost | Part 1 + Part 3 → Part 5 |
| 最终误差归一化 | 用同一批已冻结政策与全部误差裕量，给出实际 upper/lower signed error 在 `singularNormalization N` 上趋零 | Part 3 → Parts 4/5 |

最小高模数算术结论是：对于这些**确切实际** `rho_N` 和合法 `W_N,i`，对每个精度 `A>0`，有 `C,N₀` 在所有 `N≥N₀` 及全部 family 成员 `i` 之前，使 `|primeProductSignedError ...|≤C*N/log(N)^A`。现有任何源质量、PNT/Mertens、有限 density identity 或弱 Pan 定理均不能直接充当这个结论的证明。

阈值顺序固定为：有限 policy／解析裕量 → `zeta,sigma` → 共同 beta support／rough cutoff → rank、mesh、moment orders → `kappa,kappa0` → 所有请求的对数精度 → **一个 `N₀`**。不能在最后为每个 residue、history、smooth phase 或 coefficient array 分别取阈值。

## 8. 完整类型与验证入口

- [THEOREM_TYPES.md](THEOREM_TYPES.md)：新文件里全部 theorem 的原样 source signatures，含显式和隐式 binders；这不是未经运行的 `#print` 输出。
- [Part3DistributionAudit.lean](../../verification/Part3DistributionAudit.lean)：按 defining-module 元数据覆盖 public/private/generated declarations，拒绝新增公理与 unsafe declaration，传递允许项只有 `propext`、`Classical.choice`、`Quot.sound`。
- [verify_part3_distribution.py](../../verification/verify_part3_distribution.py)：精确 pin、全部五个模块 build、warning-as-error compile、bundled leanchecker replay、完整类型与公理清单；任一失败不会输出 `PASSED`。
- [part3-distribution.yml](../../.github/workflows/part3-distribution.yml)：只增加本 Part 的显式 CI 范围，未改共享根与现有 CI。

正常可执行环境中的验证命令：

```sh
lake exe cache get
python3 verification/verify_part3_distribution.py
```

`python3 verification/verify_part3_distribution.py --source-only` 仅产生 `SOURCE_ONLY_NOT_COMPILED`。它既不运行 Lean，也不证明定理成立。
