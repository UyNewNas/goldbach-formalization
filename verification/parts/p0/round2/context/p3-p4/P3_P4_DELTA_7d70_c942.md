# P0 第二轮增量回执：P3 7d70 / P4 c942

## 结论与接收身份

本回执仅审固定源码、接口和已有验证记录，没有运行 Lean、Lake、内核回放、公理审计或 CI。下列完整类型均从源码提取；编译器确认的类型清单为空。新候选不能覆盖旧模块的实际失败记录。

| Part | 固定提交 SHA | 本次增量 | 可登记状态 |
| --- | --- | --- | --- |
| P3 | 7d70a2545fd819706e473eb41e4d430ad19119d8 | 相对 64598da177adf861df3763d7c465ff941388b6d6，两个 rough SW 新模块、PrimeAP 一个证明行修复、文档及七模块验证入口更新；共 9 个文件 | SOURCE_IDENTIFIED / UNCOMPILED_CANDIDATE |
| P4 | c942b4c51d9d0005f0bd566906a3f0c88eeb1dba | 相对 262f69822a386a9d44efc059bceba11049668d68，仅 docs/PART4_UPPER_HANDOFF.md 增加 355 行 | 文档更新；五模块 proof checkpoint 仍为 262f69822a386a9d44efc059bceba11049668d68 |

共同证明基线仍为 1a80c1bcce67886f699d097fc37fd245cd3620bf，手稿仍为 ba6ec11d800eccc54406490631895e174de85766。GitHub 两次固定 compare、逐文件 blob 与 SHA-256、源码类型及未闭合输入均写入同名 JSON。其他 intake 提取的五个固定文件已由本审查员再次重算 hash；另直接读取了 P3 新审计和脚本，七个文件身份全部匹配。

本轮没有改变工具链、依赖、定义、量词、常数、数学代码、源分支或公共根导入。

## 1. P3 新增候选实际做到了什么

### 同一误差与辅助互素过滤

新定义 auxiliarySWError 使用同一有限载体 S、同一复系数 alpha、同一精确 coprime mean：
E(k,q,b) = sum_{n in S, n=b (q), (n,k)=1} alpha(n) -
sum_{n in S, (n,kq)=1} alpha(n)/phi(q)。
MediumAtom.auxSWError_eq_auxiliarySWError 是这些对象的字面一致性候选。

若 S 是正整数前缀 Ioc 0 H 的子集、一有界非零系数只支持于所有素因子都大于 z 的整数，删除辅助互素条件的代价有显式证明候选：
norm(E(k,q,b)-E(1,q,b)) <= 2*omega(k)*H/z <= 2*tau(k)*H/z。
这里 H 是绝对上端点，不能当任意平移区间的长度。k、q 为任意正整数，b 任意，没有隐含的 k 上界或 SW 假设。

证明体从真实有限和相减的 -A+B/phi(q) 出发，以 p|k 且 p>z 的倍数覆盖被删除的非零系数。实际 roughOneSlot 与实际 ArithmeticFunction.moebius 组成的 roughMoebiusSlot 有实例候选。Mellin 扭转的版本允许任意实 t，但只证明这一删除代价；不提供任意频率的小模数 SW。

### 大模数分支与统一归一化

另一个有限估计对任意一有界复系数给出
norm(E(k,q,b)) <= H/q + 2 + H*cR*log(H)/min(q,H)。
它不要求 roughness、SW 或原始余数，且允许 q>H；所复用的是 pinned reciprocal-totient 标量界，不是将 prime SW 当 rough composite SW。

归一化模块证明候选使用手稿的原 cutoff x^(1/(log log x)^3)，把辅助 k 的误差支付为任意 log accuracy，阈值先于所有 MediumAtom、载体、系数、k、q、b。大模数 q>=log(x)^(A+2) 的分支在固定 xi>0、x^xi<=H<=2x 下也被支付；任意 k 的代价由 tau(k) 的固定一次幂覆盖。

原 MediumAdmissible 已有 1<=Q1<U*x^(-sigma)，故 alphaScaleLower 推出 x^sigma<U，不新增参数范围。最后的 uniformAuxiliarySW_of_mediumAdmissible_small_moduli 把完整辅助 SW 缩减为同一实际族、k=1、q<log(x)^(A+2) 的统一小模数 SW。这个缩减有真实有限估计支撑；它仍显式要求尚未证明的 hSW。不能登记为完整 SW、signed medium、prime-product 分布或 hUpper/hLower 已完成。

### PrimeAP 精确修复

Part3PrimeAPDistribution 只把 part3_abs_sum_mul_primeAPIntervalError_log_saving 中一个证明行的 (abs_sub_le _ _).trans 改成 (abs_sub _ _).trans。逐字比较确认除此之外全文件不变；所有源码定理头相同。这里原调用是错误的三点三角不等式形状，目标需要两项绝对值界。修改不改变常数 2、区间、BV cap、定义或量词。此版本没有经过本环境编译。

P3 7d70 没有改动 LongSlot 两模块，不能将该提交自身“未定位确定错误”的静态说明替代 P0 之后得到的真实 LongSlot Lean 诊断。

## 2. 对同一实际 rho / realPhysicalDistributionError 的影响

P4 的消费对象仍是最终 Q delta N、rho delta N 逐物理模数加权的真实两素因子源误差。其 realHalfProductSource 对应 r<=q、T<=r*q<=N、严格 q^b<r 的有序素数表示；prime squares 要保留，没有未经证明的除以 2。

新辅助 SW 是单槽 n≡b 的精确 coprime-mean 误差，虽然中心定义方向兼容，它不等于 P4 的两素因子源，更没有实例化最终 rho。两新模块不依赖 LongSlot，也未把无 rough 过滤的长整数槽结果升级成 rough 长槽。

因此本轮减少的是 restricted-medium 的一个前置输入：未来只需为同一实际族补 k=1 小模数 SW，再使用有限减少。下列实质步骤仍未闭合：

- P1/P3 实际图册与系数实例化：本地 cutoff 被实际 chart cutoff 支配、共同区间、系数一有界规范化、许可频率和 variation 预算。
- 真正的小模数 roughOne / roughMoebius SW，且常数必须先于实际原子、区间和许可相位。prime indicator 的 SW 或形式 Dirichlet 级数恒等式不能代替它。
- restricted-medium 的 signed dispersion / spectral 核心，后续两素数图册、平滑、归属、截断和 collision 预算。UniformAuxiliarySW 本身不推出 RestrictedMediumObligation 或 UniformPrimeProductTarget。
- 从该实际 signed prime-product 和到同一个 realPhysicalDistributionError 的准确有限重排和所有边界代价，并保持最终 Q、rho、实数 b、cutoff 与精度相同。
- 若采用正 outer-source，现有 P4 桥要求整个外载体 m<=N，且须另供正权、mass、coprime correction 和同 rho discrepancy；跨 N 的光滑 cover 需要正确整数 shift 处理。

P4-B 的 hdistribution 仍未获供应者；P5 的实际 switched family、marked-product masses 及同权分布也未闭合。P5 只等待 P4-A 的真实 K 输出，不等待 P4-B；本轮没有任何新 K 输出。

## 3. P4 c942 新说明对各 Part 的约束

### 真实积分、上包络与归一化

现有 raw-density 组装器的 hIntegral 是归一化实际 raw density 的精确 Tendsto。如果 P1 去掉非负 savings 后仅给上包络，该上包络不能充当精确极限。应从实际供应者建立 eventual inequality 或 limit-comparison 适配。P2 必须明确证书核验的是精确 functional 还是上界；P0 不以新包装结构吞掉这一缺口。

组装器使用 log(N)/C_N 归一化。若上游按 D=N^nu 的 log(D) 表示系数 U，转换到 log(N) 系数是 U/nu；已有误差转换不自动转换另一个主积分。epsilon 固定时，小 Rosser attachment 的固定误差不会仅因 N 增大而消失。

### 共用载体、斜率及 compiler reserve

实际 raw 支持 Rraw 与较大 compiled 支持 R 还需要有限 zero-extension 适配：Rraw subset R，raw 在新增位置字面为零，且使用相同 small weights，证明 supportedDivisorSum、smallRoughRho 和 physicalDensitySum 不变。后续密度分解仍须同一 cutoff 的 small/rough support。该 adapter 尚未实现，不是已交付的 P2 分析预算。

已有实际小 Rosser sandwich 可给两侧绝对斜率 M=V*(1+Esmall)，V>0、Esmall>=0；lower density 可以为负，仍须绝对值。compiler 义务是 M*sum |compiled(d)-raw(d)|/phi(d)，不是有符号差值或仅用 V 的预算。

账目应保留 rawBound=E、densityCap=E+u、compilerReserve=u、E+2u<=K；已在上游支付的 partition、history、truncation 代价不得重复计入。真实积分、compilation error 和余量不由纯有理账目替代。

### Coarse chart 闭角与算术边界

P4 对 P2 的 AboveMuSecondCoarse 指出 k=1、u=v=1 的闭角：
chartY=oldResidual=newResidual=19/96，所以 ratio=1。现有紧区域 supplier 要求严格 1<s，不能覆盖整个闭图册。需要可许可的内部近似及统一算术边界 reserve；仅说该边界 Lebesgue 零测不够。

这不是宣称 P2 数值首格有反例。它把实际 first-exit domain 与 chart 的对应、边界 ownership 和算术计数责任交回 P1/P2/P4 接口。Pullback factor 4 的兼容性也不等于域匹配已证。

### 参数量词

P4 counting 条件桥先固定 b、kappa、sieveExponent，再量化所有 delta>0。同一精度下 majorant、density、coprime correction、distribution 四项必须使用同一 Q、rho、cutoff、支持和 sieve 参数。若实际供应者在 delta 之后选 kappa 或 sieveExponent，需在有限应用中证明适配；epsilonMax 本身不提供图册 licence 或 P3 估计。

## 4. 验证范围、旧失败及分批接收

本增量没有进行编译、内核重放、公理检查，也没有触发 Actions；P3 新文档的编译器确认清单为空，P4 仍记录启动前阻塞。先前 runner_id=0 / steps=[] 的 Actions 记录保持原身份，没有登记新 CI 成功。

P3 新验证入口明确列出七个模块，不过 Part3DistributionAudit.lean 仍在非 module 文件写七行 import all，旧 pinned-parser 静态问题仍存在。旧五行 import 修复补丁不能声称已完整修复新审计；应将这七项改成正常 import 并修正说明，再在固定修复 SHA 严格执行。这是源码审查建议，未运行 Lean 获取新诊断，也未在本轮修改审计。

P0 已执行过的原 LongSlot strict 编译仍为 exit 1：首处是 177:4 的 letI strict linter，随后 189:61 有 coprimality 目标未解。P0 仅改证明体的候选 SHA-256 是 67ccc48e6a4befadfd4b5639e2cdb4bd43e443b8f4eaf3086fe5a6c5fbd0023e，12 个定理头和 6 个定义正文不变，待根排期复编、回放和统一公理盘点。没有成功信号中止证据，不能记为 ABORTED；P1 没有被操作。

建议接收顺序：

1. 将 P4 c942 作为文档约束接收，五个 Lean 模块继续绑定 262f proof checkpoint。
2. 将 P3 PrimeAP 一行修复作为独立未编译候选，与原 64598 源版区分。
3. 排队显式验证 ImbalancedChen.Part3RoughAuxiliarySW，再验证 ImbalancedChen.Part3RoughAuxiliarySWNormalization。先按新源重新 plan、核对已完成缓存和 P1 同版本运行状态；本审查没有把旧 plan 的 pending 数字移植到新模块。
4. LongSlot 候选继续独立等待串行槽；新 SW 模块不会使它原失败消失。
5. 所有新已核验组件列表为空；源码接收与证明验收分列。根入口由 P0 统一修改。

最小新增/修复显式目标为上述两个 rough SW 模块及 ImbalancedChen.Part3PrimeAPDistribution；七模块 audit/runner 的覆盖范围不能由旧根 lake build 成功替代。

## 5. 关键完整源码类型

以下声明来自固定 P3 7d70。namespace 为 ImbalancedChen.Part3；逐一保留原始前提、量词、常数。全部 29 个源码 theorem 声明头（含 2 个 private）另存 p3-7d70-rough-sw-source-types.md 和同名 JSON 本文档的 source_theorem_types 字段；不含编译生成声明，不能代替 owned-declaration 公理审计。

### auxiliarySWError_sub_one_norm_le

```lean
theorem auxiliarySWError_sub_one_norm_le
    (S : Finset ℕ) (α : ℕ → ℂ) (H k q b : ℕ) (z : ℝ)
    (hS : S ⊆ Finset.Ioc 0 H) (hz : 0 < z) (hk : 0 < k) (hq : 0 < q)
    (hα : ∀ n ∈ S, ‖α n‖ ≤ 1)
    (hrough : ∀ n ∈ S, α n ≠ 0 → ∀ p : ℕ,
      p.Prime → p ∣ n → z < (p : ℝ)) :
    ‖auxiliarySWError S α k q b - auxiliarySWError S α 1 q b‖ ≤
      2 * (k.divisors.card : ℝ) * (H : ℝ) / z
```

### auxiliarySWError_sub_one_norm_le_mellin

```lean
theorem auxiliarySWError_sub_one_norm_le_mellin
    (S : Finset ℕ) (α : ℕ → ℂ) (H k q b : ℕ) (z t : ℝ)
    (hS : S ⊆ Finset.Ioc 0 H) (hz : 0 < z) (hk : 0 < k) (hq : 0 < q)
    (hα : ∀ n ∈ S, ‖α n‖ ≤ 1)
    (hrough : ∀ n ∈ S, α n ≠ 0 → ∀ p : ℕ,
      p.Prime → p ∣ n → z < (p : ℝ)) :
    ‖auxiliarySWError S (fun n => α n * (n : ℂ) ^ (Complex.I * (t : ℂ))) k q b -
      auxiliarySWError S (fun n => α n * (n : ℂ) ^ (Complex.I * (t : ℂ))) 1 q b‖ ≤
        2 * (k.divisors.card : ℝ) * (H : ℝ) / z
```

### auxiliarySWError_norm_le_large_modulus

```lean
theorem auxiliarySWError_norm_le_large_modulus
    (S : Finset ℕ) (α : ℕ → ℂ) (H k q b : ℕ)
    (hS : S ⊆ Finset.Ioc 0 H) (hH : 3 ≤ H) (hq : 0 < q)
    (hα : ∀ n ∈ S, ‖α n‖ ≤ 1) :
    ‖auxiliarySWError S α k q b‖ ≤ (H : ℝ) / q + 2 +
      (H : ℝ) * MathlibNt.SieveTheory.Richert1969.richertReciprocalTotientConstant *
        Real.log (H : ℝ) / (min q H : ℕ)
```

### eventually_auxiliarySW_large_modulus_logAccuracy

```lean
theorem eventually_auxiliarySW_large_modulus_logAccuracy
    (A epsilon xi : ℝ) (hepsilon : 0 < epsilon) (hxi : 0 < xi) :
    ∀ᶠ x : ℝ in atTop, ∀ H k q b : ℕ, ∀ S : Finset ℕ, ∀ α : ℕ → ℂ,
      S ⊆ Finset.Ioc 0 H → x ^ xi ≤ (H : ℝ) → (H : ℝ) ≤ 2 * x →
      (Real.log x) ^ (A + 2) ≤ (q : ℝ) →
      (∀ n ∈ S, ‖α n‖ ≤ 1) →
      ‖auxiliarySWError S α k q b‖ ≤
        epsilon * (H : ℝ) / (Real.log x) ^ A
```

### MediumAdmissible.alphaScaleLower

```lean
theorem MediumAdmissible.alphaScaleLower
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) :
    d.scale ^ sigma < d.U
```

### uniformAuxiliarySW_of_mediumAdmissible_small_moduli

```lean
theorem uniformAuxiliarySW_of_mediumAdmissible_small_moduli
    {ι : Type*} (F : ι → MediumAtom) (B : ℕ) (sigma kappa c0 : ℝ)
    (hsigma : 0 < sigma)
    (hadmissible : ∀ i, MediumAdmissible B sigma kappa c0 (F i))
    (hSW : ∀ A : ℝ, 0 < A → ∃ C : ℝ, 0 < C ∧ ∃ x0 : ℝ, 1 < x0 ∧
      ∀ i : ι, x0 ≤ (F i).scale → ∀ q b : ℕ,
        1 ≤ q → (q : ℝ) < (Real.log (F i).scale) ^ (A + 2) →
        Nat.Coprime b q →
        ‖(F i).auxSWError 1 q b‖ ≤
          C * (F i).U / (Real.log (F i).scale) ^ A) :
    UniformAuxiliarySW F 1
```

## 6. P4 同一 rho 消费端完整源码类型

此类型仍来自 proof checkpoint 262f69822a386a9d44efc059bceba11049668d68；c942 没有修改它，四个显式分析输入均保留。

```lean
theorem eventually_RealB_le_currentK_log_of_same_rho_inputs
    {b kappa sieveExponent : ℝ}
    (hb : 0 < b) (hb1 : b < 1) (hkappa : 0 < kappa)
    (hsieve : sieveExponent < 1)
    (Q : ℝ → ℕ → Finset ℕ) (rho : ℝ → ℕ → ℕ → ℝ)
    (hmajor : ∀ delta : ℝ, 0 < delta → ∀ᶠ N : ℕ in atTop, Even N → ∀ n : ℕ,
      (if Nat.Coprime n (sieveProduct N (Nat.ceil ((N : ℝ) ^ sieveExponent)))
        then (1 : ℝ) else 0) ≤ physicalDivisorSum (Q delta N) (rho delta N) n)
    (hdensity : ∀ delta : ℝ, 0 < delta → ∀ᶠ N : ℕ in atTop, Even N →
      physicalDensitySum (Q delta N) (rho delta N) ≤
        (currentK + delta) * (singularSeries N / Real.log (N : ℝ)))
    (hcoprime : ∀ delta : ℝ, 0 < delta → ∀ᶠ N : ℕ in atTop, Even N →
      |realPhysicalCoprimeCorrection b N (manuscriptHalfProductCutoff kappa N)
        (Q delta N) (rho delta N)| ≤ delta * singularNormalization N)
    (hdistribution : ∀ delta : ℝ, 0 < delta → ∀ᶠ N : ℕ in atTop, Even N →
      |realPhysicalDistributionError b N (manuscriptHalfProductCutoff kappa N)
        (Q delta N) (rho delta N)| ≤ delta * singularNormalization N) :
    ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ N : ℕ in atTop, Even N →
      (RealB b N : ℝ) ≤
        (currentK * Real.log (1 / b) + epsilon) * singularNormalization N
```

## 7. 固定源文件身份

| 固定 SHA | 文件 | Git blob | SHA-256 |
| --- | --- | --- | --- |
| 7d70a2545fd819706e473eb41e4d430ad19119d8 | ImbalancedChen/Part3PrimeAPDistribution.lean | 2d761133b313302ab3a89ae906eb6944037a093d | 55319b7e1150799a5bd2ed4bcc0ef3dd486de57409d9b859f678c068bcb8c7fc |
| 7d70a2545fd819706e473eb41e4d430ad19119d8 | ImbalancedChen/Part3RoughAuxiliarySW.lean | 7ac03bfc01b00b228fb108bf1186ef45302b8344 | d1ff2dc2e0ce6f9f5e18eb2b01da4ae10dfb42c23d2d49f1bb241f8c7796a9f8 |
| 7d70a2545fd819706e473eb41e4d430ad19119d8 | ImbalancedChen/Part3RoughAuxiliarySWNormalization.lean | 60bd8f19aa6733851fbfc43b2afb269a97fa1ed3 | 1d1a6e5d23449f3733a7532018ea23ae820bab06a8c45d46476cc9f2a6b7f91c |
| 7d70a2545fd819706e473eb41e4d430ad19119d8 | docs/part3-distribution/ROUND2.md | 73e37b8bb22662f0e335ffe8ce0f29f3de30f7f7 | dfb6c403bc1d2026c22868b4495763fe5524bd2b0beecb37e15fe83f5522da17 |
| c942b4c51d9d0005f0bd566906a3f0c88eeb1dba | docs/PART4_UPPER_HANDOFF.md | dc45388237e66dfbbb1b4b92f034c624da25dcd0 | 8f44c95be95ddbd9d4323f678fff2ecce94d95956b2d07e3340b611f8150bfdc |
| 7d70a2545fd819706e473eb41e4d430ad19119d8 | verification/Part3DistributionAudit.lean | 6430421b3c3feb2966f33af937ace94d316eb371 | 5b47d8caa0bd79ba9f1a529134cd63feafb8c27eb80f27b9073c24c5fc18b89d |
| 7d70a2545fd819706e473eb41e4d430ad19119d8 | verification/verify_part3_distribution.py | bc70845647cb358202d02221b8c0f2174be8a66f | 901c6602aa339edea8e19167172bda22496bd792e8e47fa4da9ee09cbfbf3644 |

来源：固定 GitHub compare 的完整回执见 delta-github-compares.json；每个固定源码 URL 见同名 JSON 的 source_identity。本文仅引用这些固定内容，无新增编译证明断言。
