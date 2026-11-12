# T07 · 原第二种子的七个普通项与同载体素数限制

原 U3、U4 任一冻结根和实际正种子集合 `S = seedPositions N n r t p` 上，令 `C = Σ_l m_l trueAt(l)`，令 `Θ = markedTheta S`。八份源码给出以下有向界。两个非负量分别是三个负单素数原计数减下 Rosser 多项式的总额 E⁻，以及四个好双素数上 Rosser 多项式减原计数的总额 E⁺。初始行和四次反馈共享一个在目标之前选取的 T。[最终声明](Part5OriginalH430SeedSameCarrierPP.lean)

~~~text
5[C − (1 − 1/50)Θ] + E⁻ + E⁺
    ≤ ordinaryAP(S) + switchedPPBalance(S) + εΘ

5[C − (1 − J_(j+1))Θ] + E⁻ + E⁺
    ≤ ordinaryAP(S) + switchedPPBalance(S) + 5 J_j Σ_l m_l F_l + εΘ    (j = 0,…,3)
~~~

`ordinaryAP` 保留两个 Γ1 上筛锚的 4∶1 原系数，扣去 Γ2–4 的三个 π 居中带符号 AP 余数，加上 Γ5–8 四个好双素数原截点的带符号上筛 AP。F 是原三个单素数和四个好双素数窗的物理反馈，已含 1/5。两式直接使用原 1/50 及四个有理轮次值。正部的中间传递可以取任一深度和任意实际标记子集 B，种子计数结论以规定的 S 为范围。[标记普通项](Part5OriginalH430SeedMarkedPositiveAP.lean) · [七窗 AP 端点](Part5OriginalH430SeedSevenOrdinaryAP.lean)

## 好 Γ5–8 的原计数和积分

同 Q 直接保留 Γ5、6 的固定截点与 Γ7、8 第一颗素数的截点。对真实素数对，Γ6、7、8 的两个平方门在原半开窗口上均严格成立。Γ5 的第二颗素数亦满足原平方门，其余拒绝条件精确化为 Q ≤ d p²q。按原有序素数对重新索引后，该项就是 `originalBadPairCount`，斜边等号仍归原坏计数。[原拒绝计数](Part5OriginalH430SeedRejectedPairCounts.lean)

实积分使用同一核 1/[uv(1−u−v)]。在 [50/227,10/29] × [50/227,25/61] 上三因子均保持正值，故可以对原条带作 Fubini。Γ5 全三角的坏纤维从 u=19/58 起，v 下限为 max(u,1−2u)，在 1/3 处切换。非零线性型 v+2u 的实水平集为 Lebesgue 零测集。由此原好 Γ5 积分恰为全三角减去见证的原两块坏积分。Γ6–8 分别为原矩形、三角形、矩形。四个普通主项的总和逐项抵消旧 `signedPositive` 中相应四项。[原核与有限维 Fubini](Part5OriginalH430SeedPairRealFibres.lean) · [四项完整等式](Part5OriginalH430SeedOrdinaryFourIntegral.lean)

原正母项含两条直接双素数窗，另有 Γ7–21 的原切换母词表。按原长度切出 Γ7、8，再逐词用旧掩码商与独立正素数算术标签的双射处理长词。Γ9–21 保留原 13 组的全部 20 次颜色词出现，以及 Γ20、Γ21 的单位尾数。原坏 Γ5 另计一类。母项到四个好计数之间的原补集误差由前代的同 Q `all36_charge_theta_payment` 支付。[各原词来源](Part5OriginalH430SeedThirteenPrimeWords.lean)

## 已定价的粗整数与真实 PP 还差什么

对指定词 l，在 D = d·prod(l) 和原截点 z 取单一集合 `roughNumbers (N/D) z`。坏 Γ5 用父截点，长词用原倒数第二颗素数。将其中每个正整数 m 赋权 1 就是原转换的未测试质量；在同一组 m 上加 Dm < N 与 N−Dm 为素数的测试就是 `p5z_labelledPrimeMass`。在原绝对粗接收子集，映射 ℓ ↦ (N−ℓ)/D 有逆 m ↦ N−Dm。旧掩码允许的前缀重复、以及粗商与 N 不互素的中心例外，在输出素数限制仍在时按原标记真实累加。既有 `exact_errors_theta_payment` 将这 21 类的两组例外合计压到 εΘ。单位 m=1 保留原价。[同一集合及双射](Part5OriginalH430SeedPurifiedPrimeFibres.lean)

最终的 `switchedPPBalance` 为 Σ_l m_l 乘“该位置 21 类实测质量，减去 (681/100)/4 乘该位置原 thetaConversion(N,d) 及相同 21 类未测原质量”。标签、词次数、截点、d、N、Q、测试前的整数集合均可在表达式中逐项对齐。换回原 `converted` 的等式在任意有限 D 与任意实 σ 下成立。这里完成了原 PP 调用的两个计数对象及其系数配对。[原转换等式与最终端点](Part5OriginalH430SeedSameCarrierPP.lean)

## 尚未支付的责任

- 原始正种子的真实计数仍欠选中标记族上 `ordinaryAP + switchedPPBalance − E⁻ − E⁺` 的有向小量控制。普通部分要求对实际冻结词、权与同 Q 的 AP 多项式聚合。切换部分要求原固定正截点产品分布许可和与密度证明相同的 ρ 承担真实 PP 误差。有限上筛恒等式与已得粗整数质量只给这些调用的对象和其普通主项。
- 四轮另需用较早轮的实际子计数供应原三单、四双的增益，以支付右侧的 5 J_j ΣmF 和对应非负余量。文稿中 0.020249 与 13/100 所给的标量及七窗质量已在之前的原证书和物理窗口中对齐。四次迭代作为真实计数上界仍开放。
- 一般 36 个 W2 行的转换价格、70 个 W1 行的切换 PP、固定锚和前代实际计数、整套 430+11 步与最后 U3/U4 h34 接口保持开放。此前 106 行端点与 144 个好对的普通上筛出账见已封存包。[106 行](../REPORT.md) · [普通种子](../ordinary_rosser/REPORT.md) · [144 个好对](../pair_rosser/REPORT.md)

原稿在 `proof-library/source/second-seed-omega-certified.tex` 与 `second-seed-certified-finite-feedback.tex` 给出斜边、原切换范围与 K=6.81 的分布引用。沿用原见证，无新增数值包。此处八份源码只完成静态查读及字节封存，远端内核回执、独审和上述分析责任分别登记。[来源、完整声明和 SHA](REGISTRY.json)
