# G1 在历史 d₊ 系数上的第十三笔收入

复核 T05 的 `P4AOriginalHistoricalFourthPaidDensity.lean`，9162 字节，SHA256 `52c53aa995d40408935a22755915e816796c510e391d0bb06db8d3e5fa539726`。作者 REGISTRY `e2db49b3a1d15ef83d10d786417a0e465ec75b01690e50f12cc6ea369be9284d`，REPORT `62a69afcdff7f747b5b58b1836fe72154ca6b4fdab4d7e9650c3d0de45888a6d`。直接来源为已审 T03 的 `6697cc6e…` 与旧第三正根同系数终端 `9fbffe34…`。

原始强第四扣项 10601625247768616959055/2^78 是 currentUpperEighteenGains 0。此前 `beforeEight` 中出现的原第四积分正是 T03 所证 originalFourthIntegral (original e q a)。既有第一至第四数据、资格和前沿在并入新第五数据时保持相同，故这一旧侧积分可入同一扩大第五 bank 的实际负项。replace_fourth 只用严格 G1−η/2<I₄，将 −I₄ 上界为 −G1+η/2。旧终端取 η/2，一共给 η。原归一化正比例、归档 G15–22、实际 presieve 修正、余下的第五 requant 及第六变更不改符号。

完整顺序是 r、n、a、e、q，随后 ν、β、τ，最后目标 N。原 a≤1/800 可直接用于 G1 的 a≤3/200。e 阈值取两个正数的 min，在当前 e,a 取得 G1 的 qG，再以 max(qMin,qG) 送入旧终端。对其所有 q≥q0 同时满足两个原不等式，不依赖目标或再挑物理素数。positive-presieve 和 finite count 各继承自身原证明的同一 β。物理费用只使用旧终端的一次 u_c。

由此 `exists_paid_density_and_count` 在旧 D₊、旧 tagged ρ 上包含四正项及 G1、G2、G3、G5、G6、G15–22 共 13 项，保持所有非零模数 <N^0.599、同 Q/ρ 的实际密度和 RealB 上界，后者有显式未付的带符号 distribution error。尚欠 G4、G7–14、整第五/六改变量及独立密度余额。修正的全有序第三表采用新根和区间矩形后的另一 ρ，需另证这些实际支付传至该系数。这里为旧系数的精确源码职责，无新绿色与全局 hdensity 结论。
