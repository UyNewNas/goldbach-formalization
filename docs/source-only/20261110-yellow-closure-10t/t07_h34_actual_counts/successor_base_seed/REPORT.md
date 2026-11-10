# T07 · 原始 430 行基数与采用种子的物理计数

**26 份 Lean 候选源已冻结。** 主终端覆盖原 U3/U4 两个母词、同一真实 `Q` 下的 106 个获选动作、全部 `g<430` 以及行取整损失。70 个 W1 存储基数已经接到真实无筛粗整数主项和同一载体上的加性素数限制。36 个 W2 普通项及种子特定行的转换整数主项已接到真实子计数。原始加权分布调用、一般 W2 转换行、前代计数及 430+11 的最终归纳仍待证明。状态为 source-only。全源指标为 `98f85bac5cc19c41a35fa4d3f09596f04b876f1bbbfb3bca26ef476ef17dff27`。

## 原终端

对任意 `ε>0` 先取一个 `T≥4`。对所有偶数 `N≥T`、两个原根、原素数带内的 `p`、`0≤t≤1/12`、网格 `1/(n+1)≤11/384`，及每个 `g : Fin 430`，有以下单侧比较。每个动作 `a` 的位置集合 `S_a` 是同一冻结选择器在原路径 `l` 上实际选中该动作的带标号位置。

```text
Σ_a Σ_{l∈S_a} m_l (trueAt_l − θ_l (A⁺(s_l) − requestValue(iterate(g+1),l)))
  + selectedBankRoundingLoss
≤ Σ_a Σ_{l∈S_a} m_l finalDebt(N,Q,L_l,d_l,g,a) + ε actualBankTheta.
```

`trueAt` 是原加性素数 `ℓ₀` 的商 `(N-ℓ₀)/d_l` 在该位置自身截止点的真实基数，`d_l` 是完整旧素数词的乘积，`Q=d_lN^{L_l}`，`θ_l=thetaAtom(N,Q,d_l)`。`actualBankTheta` 是同一标记和 `Σ_a Σ_{l∈S_a} m_lθ_l`。固定、普通和转换项同用这个 `Q`，各子项使用各自真实的子 `θ`。同标签不同历史仍按原次序和标记求和。空族及零质量无需除法。前代固定读保留指定闭胞，普通移动读保留结点相邻最小值、区间及外部零值。冻结时 T03 收到平方异常两源，T09 收到全量索引。审查结论以各自另存的冻结记录为准。 [106 行终端](Part5OriginalH430BankAfterW1PrimeRestriction.lean) · [旧行与取整](Part5OriginalH430AllBankSignedCounts.lean) · [原商计数](../Part5OriginalH430HistoryQuotientCounts.lean)

## W1 的原有 70 行

对 `s=12/5+i/10`、`s_0=16/5+j/5` 写 `z=(Q/d)^{1/s_0},w=(Q/d)^{1/s}`。原三素数不等式有一个固定前代上项，负一素数项和正三素数项的系数均为 `1/2`。在实际历史上 `P^-(d)≥w`。普通负项逐素数使用原 `A_-(s_0(1-u))` 和原前代小写 `h`，子 `θ_{dq}` 留在实际求和中。原 `A_-(v)` 在所需区间等于 `log(max(1,min(3,v-1)))`，原 `A_+(s_0)=1+J(s_0)`。[普通核](Part5OriginalH430OrdinarySingletonKernel.lean) · [真实负项](Part5OriginalH430BankOrdinarySingletons.lean) · [W1 计数](Part5OriginalH430W1SignedOrdinaryBase.lean)

正三素数保留 `z≤a<b<c<w`、目标及旧乘积互素、实际 `α=log(N/d)/log(Q/d)≥2`，Buchstab 核的分母是中间变量 `u_b`。原转换积分为

~~~text
∫_{1/s₀ < uₐ < uᵦ < u𝚌 < 1/s} ω((α−uₐ−uᵦ−u𝚌)/uᵦ) / (uₐ uᵦ² u𝚌) du .
~~~

整立方上 Buchstab 的参数至少 `2s-3`。复用既有全局上界和真三角矩原函数，所得 `M=(70893/125000)((s_0+s)log(s_0/s)-2(s_0-s))` 正是原程序使用的上包络。真实转换质量由 `#{m:0<m≤N/(dabc),P^-(m)≥b}` 对全部有序三素数求和，再乘原 `thetaConversion(N,d)`。原始 `m=1` 保留。中间素数处在固定正幂以上，`α≥2` 保证高度 `x≥b`，故 `log b/b→0` 一致地支付 Buchstab 上界的单位项。目标删除后的真实三素数和由原 PNT/Mertens 素数箱极限传到同一个中间变量核。[Buchstab 积分](Part5OriginalH430W1SwitchedBuchstabIntegral.lean) · [真实三素数和](Part5OriginalH430W1ConvertedPrimeQuadrature.lean) · [含单位的粗整数](Part5OriginalH430W1InclusiveRoughCounts.lean) · [原标签双射](Part5OriginalH430W1PhysicalRoughDictionary.lean)

原 430 组的历史 `K_table=6761767/10^6`，当前 `K=8452171/1250000`，种子组另外使用 `K_seed=681/100`。程序 0025 给出的通式是 `−J(s_0)+ordinary−K·M/8`。原表以当时使用的 K 生成，后续校准行将下界调整到 430 组的历史系数。0590 对原 70 个记录、两组校准基数和正质量的斜率分别复查。0504 存原组的 375/430 两个 `K` 及原行。新源直接以最终 430 行整数乘 `2^{-80}` 为左边，把真实普通项和 `K_table·M/8` 相接。对每个普通积分在 `1/s_0` 到 `min(1/s,1-2/s_0)` 做下包络，遗漏尾部普通核非负。对真实 `J` 做上包络。两个区间各用 32768 个有向 Q80 单元。正三素数质量另用 48 项对数上界。10 个 `J` 合法性、全部 70 行联合合法性及终值不等式写成封闭证明体。本机没有运行这些有限体，真值、远端资源及 elaboration 均待验。原 0590 的独立复查使用 256 项 `J` 级数、64 格复合 Simpson 和四阶余项、384 项质量对数，比对证据的原字节已登记。 [原基数和真实积分](Part5OriginalH430W1OriginalBaseEnclosure.lean) · [真实转换付款](Part5OriginalH430W1TrueConvertedBase.lean) · [原程序和回执](REGISTRY.json)

**第一素数重复项。** 原三素数计数在中间素数 `b` 处筛余数时用掩码 `(dN)a`。原 `P2W1UnsiftedPrimeProductSource` 从已经绝对 `b`-粗的正乘积词出发，无法单独解释这个豁免。用原 `tripleCarrier_eq` 在同一加性素数和旧商上翻转有限关联矩阵。若尾部 `m=(N-ℓ₀)/(dabc)` 含素因子 `r<b`，则 `r∤dN`，因而 `r=a`，于是 `a²∣(N-ℓ₀)/d`。三个实际标签均为这个正旧商在原窗口内的素因子，各至少 `N^η`，`η=frozenResidualFloor/5>0`。对每个 `ℓ₀` 标签重数至多 `(1/η)^3`。原 `weightedSquareEvent_theta_payment` 付款后，`rawTripleCount` 至多等于绝对 `b`-粗的加性素数数目加 `εθ_d`。外标记与三素数顺序继续保留。 [真实分拆及平方账](Part5OriginalH430W1FirstSquare.lean)

最末 W1 正项现在是以下带符号差，外面仍乘原位置标记。每个 `(a,b,c)` 的 `I_abc` 都是前述含单位的整数集合，`P_abc` 在同一集合中增加 `N−dabc·m` 为相应原加性素数且与 `N` 互素。W1 的原 `K/4` 与母不等式的 `1/2` 在不同位置。

```text
cleanDebt = (Σ #P_abc − (K/4) θConversion(N,d) Σ #I_abc)/2
finalDebt_W1 = fixedDebt + lowerDebt/2 + cleanDebt.
```

`prime_restriction_eq` 由原商映射的单射、`dabc·m=N−ℓ₀` 和实际正余数导出两边相等。原乘积定理所要支付的是带标记族的这项素数限制，普通前代上/下计数仍分别在固定项及负一素数项中。 [素数限制同载体恒等式](Part5OriginalH430BankAfterW1PrimeRestriction.lean)

## W2 的原有 36 行

三个负单素数核各使用原小写 `h` 对应的子下界减真实子计数。四个好的正双素数核使用实际候选集合及固定或移动 `ρ` 上的旧大写 `H`。固定 `4∶1` 上锚点与原行取整按原次数出现。每个双素数坐标为常数有理墙的等号，在真实 `Q=dN^L` 和新素数与 `N` 互素的条件下由整数幂等式排除。斜边、结点和外部读继续用原域，未从逐点严格性导出统一间距。复用已审 43 源的四个上核和 36 行原基数。 [实际双素数与有理墙](Part5OriginalH430OrdinaryPairWalls.lean) · [原好项](Part5OriginalH430OrdinaryPairCounts.lean) · [已审上核](../successor_W2Upper/REPORT.md)

```text
finalDebt_W2 = fixedDebt₄:₁ + Σ₃ lowerDebt/5 + Σ₄ childDiscrepancy/5
               + positive/5 − (ordinaryBase − Q80base) θ_d .
```

`positive` 包含真实拒绝的四个 occurrence 分支、高阶 switched、collision 与原三个 `fourthRowMotherBadPrime` 项。一般 36 行用各自原五参数，须将这些正项转为各自行可承担的有界整数质量，同时付款相应的加性素数限制。种子行的实整数 Γ5 坏部和 Γ9–21 付款已经完成，不能推广到任意 W2 参数。 [36 行真实末项](Part5OriginalH430W2SignedOrdinaryBase.lean) · [三负项](Part5OriginalH430W2SignedSingletons.lean)

## 原 `1/50` 与四轮

原文 `second-seed-stable-prefix-extension.tex`、`second-seed-omega-certified.tex`、`second-seed-finite-feedback.tex` 及 `second-seed-certified-finite-feedback.tex` 区分已获准的物理 `1/50` 计数、其一次 Buchstab 下界与四轮之前的上代许可。原程序 `certify_second_seed_first_feedback`、`certify_second_seed_finite_iteration` 的输入、程序与既有 JSON 已固定。S23 的 `actualJ2omega_gt_safe_base`、`actual_lambda_gt_thirteen_hundredths` 把 8192/4096 格的封闭 Q80 程序接到真实泛函。S16 已供应坏 Γ5 及 Γ9–19 的同 `Θ` 费用。新源补足 Γ20、Γ21 真非单位词与两个不同维数单位面，`m=1` 各自保留。给任意 `J<J₂^ω`，用严格余量导出

~~~text
J Θ_Q ≤ (ordinaryPart · Θ_Q − (K_seed/4) · converted)/5 .
~~~

对所有满足固定剩余下限的真实标记族成立。实际稳定路径自动提供所需 `d>0,Q=dN^L,α≥2` 及 `1/50` 入口的严格 `L/(11/5)<χ`。[末两 Γ](Part5OriginalH430SeedLastWords.lean) · [转换质量](Part5OriginalH430SeedConvertedMass.lean) · [原路径](Part5OriginalH430SeedHistoryMass.lean)

`actual_seed_source_debt` 把 `J=1/50` 的真实原商计数减去 `(1-J)Θ_Q`，上界是同一个带标记族的三项。第一项为 `Γ₁` 的 4∶1 锚点真差。第二项是三负项的普通主量差、原中心 `π` 的带符号 AP 余项。第三项是四个好双素数真计数及 `Γ5⁻, Γ9, …, Γ21` 的实际正素数计数减相应普通与转换质量。种子没有作为计数前提传入。 [原 `1/50` 末端](Part5OriginalH430SignedSeedCount.lean)

取 `S=11/5,s_0=227/50,(φ₁,φ₂,φ₃)=(353/100,29/10,61/25)`。三个一素数区间从 `u_*=67/227` 的原切线起，使用 `h_J=J log(S/(w-1))` 的原有效部分。四个好双素数区间使用 `H_J=J·1_{[1,S]}`，第 5、6 区切 `u+v≥117/227`，第 7、8 区切 `v≥1-16u/5`，不在坏 `D_5^-` 收益。每个素数及逐次双素数用真实的子 `θ` 和当前余因子局部修正，前后严格或闭合的窗保留。`physicalFeedback` 已含原 `1/5`，`seven_actual_on_marks` 对任一实际历史子族给出 `(13/100)Θ_Q≤Σ_l m_l physicalFeedback_l`。阈值在目标及子族选取之前。[三真实一素数窗](Part5OriginalH430SeedSingletonFeedbackMass.lean) · [四真实双素数窗](Part5OriginalH430SeedPairFeedbackMass.lean) · [逐子 `Θ`](Part5OriginalH430SeedSevenPhysicalWindows.lean)

原有理更新 `J_{r+1}=20249/10^6+(13/100)J_r` 从 `1/50` 经过四次，末值 `23273777353/10^{12}` 高于采用值 `2327/10^5`，余量 `3777353/10^{12}`。这四轮的新增结论是对每个 `r<4` 在真实初始位置 `B` 上的带符号不等式，其右侧保留原前代计数责任。

```text
5(Σ_B m_l trueAt_l − (1−J_{r+1}) Θ_B)
≤ signedAnchors + signedSingles + signedPositive
   + 5 J_r Σ_B m_l physicalFeedback_l + ε Θ_B .
```

要消去最后一行，仍须在这七组物理子载体上给出真正的上一轮上界，先经一次 Buchstab 得到一素数下界，并将这七个反馈差与相应的 `signedSingles`、`signedPositive` 有向合并。独立的初始 `1/50` 加性素数估计仍须先成立。原 4096 格证书、程序中的四个有理数及第四轮严格余量只承担这里已经指定的标量和同 `Θ` 反馈质量。 [四轮计数端点](Part5OriginalH430SeedFourMarkedRounds.lean)

## 分布调用、缺口与核验边界

- 已补的表达与可补省略包括原真实商及删除旧词、原正三素数掩码的平方例外、原 70 行 `K/8` 的成本、全 106 行固定及移动普通项、种子全部转换整数与七个物理反馈质量。固定正幂的粗整数渐近与动区间素数 Mertens/PNT 就够支付这些质量。
- 真正的独立 P3 调用是原分布定理许可的正标记盒上的带符号余数控制以及同一 `ρ` 的切换 PP。原上/下 Rosser 或 `π`-中心 AP 误差需保留符号、旧词、源素数、素数箱边界及完整平滑参数，在适当聚合后相对相同 `Θ_Q` 支付。原 PP 需针对正素数限制到本报告给出的同一无筛整数载体。文稿允许的 HB/稠密分布、Siegel–Walfisz、小量和固定大素数窗口等输入须在实际权及同一几何许可上实例化。任一固定 `d` 的原始素数差仍可有波动。所需结论是适当聚合后正标记族的估计。
- 一般 36 行 W2 转换储备仍待逐行证明。原闭胞选择与固定读有明确区别，尤其要在真实前代处理两侧、保持、输运、原先的 seed/外部/零质量入口及 U3 的结构性 `s=2` 夹断。全体 430 轮及额外 11 轮须共用有限嵌套近似，再回到原两根与 `singularNormalization(N)`。当前没有从这些材料推出整个 `h34`。
- 找到了原稿中的分布前提、原种子数的来源，以及原掩码的具体可补整数论证明。原稿给出了这些分布输入的使用条件。当前主要数学缺口是实际允许族的前代计数与分布供给。一般 W2 的实积分及转换价格比较另有独立余项。所有新文件和 27 项直接外部源均有字节映射，登记另列原文 Git blobs、旧程序、原有回执、补充原始语义及完整末端声明。未做本地 Lean、有限或数值执行。此次没有新的 kernel 回执，尤其应单独核验新 32768 格比较和 S23 既有 8192/4096 格证明体。 [完整索引与来源](REGISTRY.json)
