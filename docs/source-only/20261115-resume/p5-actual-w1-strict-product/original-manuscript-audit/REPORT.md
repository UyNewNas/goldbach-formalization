# P5.6：实际 selected W1 的最小未付正项

本轮结论是一个**明确的原实例分析 supplier 缺口**，不是新的 h34 证明，也不是源码 locator 缺口。最小对象选为原 W1 行中已命名的 `cleanDebt`。其严格三标签、整数余因子、加法素数测试和真实价格都已有精确源码；尚未找到对这一实际 selected/history 族供应所需 same-rho 分布估计的可靠实现。现有源明确保留该债务。本轮不新增 Lean 文件，不把下述待证估计作为假设再封装成结论。

相比单列“仍欠 PP”，本次把它收窄到一条可核验的原始 signed discrepancy：下面的 Δ；并区分已经供应的整数质量、有限碰撞付款、真实标签化、same-rho 解析输入及共同阈值。还核实了此真实整数载体的乘积实际上严格小于 N，因而不需要增加“避开 N”的假设或删除端点。

## 1. 唯一选取的未付项

固定原根标签 `k : Root`、同一 `RootKey c`、一代 `g : Fin 430`、原 W1 行 `(i : Fin 7, j : Fin 10)` 和原 selected box `b`。令

\[
 P=\operatorname{rootFibre}(N,n,m,k,\tau,c),\quad Q=\operatorname{cellQ}(N,n,c.1),
 \quad S_p=\operatorname{positions}(N,n,mesh,k,\tau,p,g,\operatorname{inl}(i,j),b).
\]

`S_p` 是原 `selectedLevel` 按实际 `boxOf` 过滤后的 **Fin/list 位置**，不是将整数乘积去重后的集合。对 `l∈S_p` 取

\[
 o_l=\operatorname{levelOccurrence}(l),\quad
 d_l=\operatorname{parentProduct}(o_l.current.old),\quad
 \sigma_l=\operatorname{levelMark}(l)>0,
\]

\[
 z_l=(Q/d_l)^{1/W1Anchor(j)},\qquad
 w_l=(Q/d_l)^{1/W1Target(i)}.
\]

实际历史强制 `Q=rootQ N n k tau p`；每个 RootKey 保持自己的物理 Q，不能把不同 key 的 Q 强行设成一个数。`old` 的顺序、原路径、remaining generation、owner、分支、全部 full/selected/inherited 几何过滤、两个 U3/U4 标签均保留。不同位置即使有相同 `d_l` 也分别取自己的 `σ_l`。本段没有假设某个 W1 行必定获选；空的原 `S_p` 自动给零和。

令 `T_l=primeRestriction N d_l z_l w_l`，`X_l=integerMass N Q d_l i j`，`v_l=thetaConversion N d_l`。现有 `Part5OriginalH430BankAfterW1PrimeRestriction.cleanDebt` 字面为

\[
 D_l=\frac12\left(T_l-\frac{K_{current}}4 v_lX_l\right),
 \qquad K_{current}=8452171/1250000.
\]

本轮只追踪真实标记和

\[
 D_{W1}=\sum_{p\in P}\sum_{l\in S_p}\sigma_lD_l.
 \tag{W1-debt}
\]

其中 `1/2` 是原 W1 母式系数，故整数价格为 `K_current/8`。`tableK=6761767/1000000` 是旧 Q80 base 比较常数，`K_seed=681/100` 是四轮 seed 常数；三者不得替换。`finalDebt` 仍另有 `fixedDebt + lowerDebt/2`，W2 的 ordinary/switched/base 债也没有被本项覆盖。

## 2. 真正的同一标签族

把每个 `T_l` 和 `X_l` 都写到以下同一有限标签集合上：

\[
 \mathcal L_N=\{(p,l,a_1,a_2,a_3,r): p\in P,
 l\in S_p,\ (a_1,a_2,a_3)\in
 \operatorname{orderedTriples}(\operatorname{primeWindow}(d_lN,z_l,w_l)),
\quad r\in\operatorname{roughNumbers}(N/(d_la_1a_2a_3),a_2)\}.
\]

这里严格 `a_1<a_2<a_3`，三素数均属于原半开窗且与 `d_l*N` 互素。原 `Fin 3` 字典是 `label q=(q 2,q 1,q 0)`，不能倒换中间 cutoff。`r` 是整个粗整数载体，允许 `r=1`，允许原载体中的重复素因子；不能换成一个新素数，也不能删 unit。每个标签的权仍是 `σ_l`，物理完整乘积为

\[
 F(p,l,a_1,a_2,a_3,r)=d_la_1a_2a_3r.
\]

有限求和直接给

\[
 X=\sum_{\mathcal L_N}\sigma_l=\sum_{p,l}\sigma_lX_l,
 \qquad M=\sum_{\mathcal L_N}\sigma_lv_l=\sum_{p,l}\sigma_lv_lX_l,
\]

\[
 T=\sum_{\mathcal L_N}\sigma_l
 {\bf1}_{r\in\operatorname{chenQuotientPrimeSource}(N,d_la_1a_2a_3)}
 =\sum_{p,l}\sigma_lT_l,
 \qquad D_{W1}=\tfrac12(T-K_{current}M/4).
\]

这个测试是原加法素数 receiver 的条件；不是把商 `r`、产品 `d_l` 或加法素数互相识别。若从直接 rootMask 母式出发，`E=rootMask N p` 保留在全部普通正负项中；仅对**正号**三素数项，既有 T19 `W1_raw_positive_le_receiver` 允许原集合包含关系 `E⊆receiver` 的上放大。上述 `T` 正是该已经归档的 full-receiver 上界源。绝不把这种上放大用于负单子的 lower 估计。

**实际端点核验。** `roughNumbers` 给 `F≤N`，且 `a_1|F`。原 primeWindow 给 `a_1.Prime` 和 `a_1.Coprime N`。若 `F=N`，则 `a_1|N`，矛盾；故对这个真实载体已有 `F<N`。这包括 `r=1`，没有删任何 source label，也不需要假设 receiver 非空。此简单推导解除本源的 `F=N`/自然数减法支障，但不估计 Δ，也不支付 near-N collar 的质量。

## 3. 最小 primitive supplier 与精确误差账

固定同一精度下原物理上筛系数 `rho_N` 及其实际模数载体 `Qrho_N`；这里 `Qrho_N` 是模数集合，不能和父物理实数 Q 混淆。写

\[
 S_N=\sum_{q\in Qrho_N}\rho_N(q)/\varphi(q),\quad
 X^{(q)}=\sum_{\mathcal L_N}\sigma_l{\bf1}_{(F,q)=1},
\]

\[
 \Delta_N=\sum_{q\in Qrho_N}\rho_N(q)
 \left(\sum_{\mathcal L_N}\sigma_l{\bf1}_{F\equiv N\pmod q}
 -X^{(q)}/\varphi(q)\right),\quad
 C_N^{cop}=\sum_q\rho_N(q)(X^{(q)}-X)/\varphi(q).
\]

这就是 `P5zPositiveFamilyBudget.p5z_labelledDistributionError` 在上述原标签族的实际实例。符号必须留在整个 q 和标签和里面；不要求或声称逐 q 绝对 BV、逐 d 的素数分布，或任意 σ 的分布。

已有该文件的有限 Fubini 恒等式提供

\[
 \sum_{\mathcal L_N}\sigma_lR_N(N-F)=XS_N+C_N^{cop}+\Delta_N.
\]

点态上筛与小加法素数费用 `Bsmall_N` 供应后，原 receiver 测试不大于全部加法素数测试，因而

\[
 D_{W1}\le\tfrac12\left[
 \Delta_N+C_N^{cop}+Bsmall_N+
 \left(XS_N-K_{current}M/4\right)\right].
 \tag{exact-source-ledger}
\]

这个账没有删普通 append 质量、没有借用 masked 子族的 lower 界。它把真正的分析输入定位为 **同一 actual selected W1 标签族在原 rho 下的 Δ**，而非将 `D_W1≤εΘ` 当作一个新假设。

最小需要交付的原稿分布接口是：对为上述实际有限历史族预先构造的每个许可正光滑外逼近（保留原全部标签、物理 Q/alpha、平方门和原系数），给任意对数精度 A 的

\[
 |\Delta_N|\le C_{A,\mathcal W}N/(\log N)^A
 \quad(N\ge N_0(A,\mathcal W),\quad 2\mid N).
 \tag{PP-W1-actual}
\]

光滑误差在普通完整乘积质量上的正外增量也必须在同一 root-normalized reserve 内付款。这里不能把加法素数测试先吸入 W；原稿 PP 的 W 只允许已批准的几何限制，没有额外算术筛选。`r` 到固定有限秩 prime labels 的真实分解必须保留单位项、重复因子和原 factorial；不能凭严格三标签就宣称整族只有秩三。

`P5zPositiveFamilyEventual.p5z_eventually_positive_family_upper_of_same_rho` 只是现成消费者，显式接受 `hlicensed`、`hmajor`、`hdensity`、`hmass`、`hPP`、`hcop`、`hsmall`。其中 `hPP` 仍是上式原 signed discrepancy 的输入；重新调用它不构成供应。`Part3ActualPrescribedPositiveJ` 给固定 prescribed test 的 Bessel transform 与 Schwartz decay，也不直接给此族的 `hPP`。P3J 正号 trace / uniform spectral bounds 是 medium 分布路线的上游部分；完整 medium、no-medium/long 分支及实际 W1 源的许可映射仍须分别接通。不能把一个 Bessel 变换等式称为 PP-W1-actual。

**J-limsup 的逻辑限度。** 原正乘积命题的 `(KJ+o(1))H_N` 上界与 `limsup X log N/N≤J`，本身不能推出当前 `T−K M/4` 是小量：第二个式子只有质量上界，不能向相反方向替换右端实际质量。要使用 `cleanDebt` 原价，应复用命题证明中的更早一步 `T≤XS_N+errors`，即上述 same-rho 账；或另供真正的当前质量运输。不能只把一个更宽 J 上界塞回 cleanDebt。

价格运输仍按字面

\[
 v_l=\frac{4\operatorname{li}(N)d_lC(d_lN)}{N\varphi(d_l)},\qquad
 \alpha_l=\frac{\log(N/d_l)}{\log(Q/d_l)}
\]

处理。因此 `XS_N−K M/4` 需要原 true-li / singular-factor / totient 比较及同一 rho 的 density。它是可以与 PP 分离的归一化工作；本轮未把其未经核实的方向或余项写成定理。不能重设 `alpha=2`，也不能将 PP 的完整物理规模 N 换为残余规模 `N/d_l`。

## 4. 共同阈值及 root 误差尺度

解析 PP 允许阈值依赖一个**预先固定**的几何族。正确次序是：最终 reserve 与固定原参数 → 选同一有限正 atlas、平滑/构造精度和粗素数下界 → 固定同一精度的物理 rho → 取所有有限原 query/action/owner/cell 的一个最大 N0 → 量化所有更大的偶数 N 及其原标签 p、位置 l、三素数和余整数。不能先看 N 或某个算术 fibre 再选成功的 selector、rho、interval 或 phase。

430 代及另 11 根必须共用原预选 atlas 和阈值；不能把逐个固定 p/l 的阈值取最大来冒充这一结论，因为这些标签随 N 变化。既有有限 collision 估计具有更强的 `N0` 先于 n、tau、位置的量词，但不能把这个量词顺序自动转移给依赖平滑族的 PP。

普通 PP 的绝对 `o(H_N)` 可以在有限原查询和根的 reserve 中分配；它不自动成为所有空或稀薄 selected box 的 `ε·boxTheta` 相对误差。若使用每个 box 的自身 Θ，必须另有相应的相对估计或对固定正极限质量的合法运输；禁止除以未证明为正的 Θ。空族在本有限账中是零，不是额外假设。

## 5. 去重和分类

| 已读可靠结果 | 实际已供给 | 不能重复冒充的缺项 |
| --- | --- | --- |
| T08 两份 actual430 源；31cce 已发表 | root receipt 的字面 if/else；append 普通数等于完整 rejectedChild | 不是普通 count/Θ 归零、不是 lower 许可 |
| T19 `ReceiptSignedPredecessors`、`OwnedReceiptNet`、`ReceiptTwoBounds` | 同 E 母式、双子正壳、有符号净账；原根直接 masked 单子空 | 不能从直接 masked 单子提取普通 lower gain |
| 19c7759d 的 `W1FirstSquare`、`BankAfterW1PrimeRestriction` | 原首素平方碰撞到 `cleanCount=primeRestriction`，保留 unit、原标记和同 Θ | 不估计 literal additive-prime restriction |
| 同提交 `W1PhysicalRoughDictionary`、`W1TrueConvertedBase`、`W1OriginalBaseEnclosure` | 实际严格三标签整数质量、真实 alpha 的积分上界、原 70 行 Q80 base 比较 | `primeDebt/cleanDebt` 仍原样在结论右侧 |
| `P5zPositiveFamilyBudget` / `Eventual` | 同 rho 有限误差恒等式及条件消费者 | 没有实际 W1 的 hPP supplier |
| T23 native L1/prime-box 与 receiver applicability；既有 Family200/经典 Γ9–21 付款 | 所声明的普通/几何/限定族误差 | 不能转授所有 deep selected W1 receiver 与 same-rho PP |
| prescribed positive-J transform | 原测试函数的变换与衰减 | 不是原 W1 分布或完整正号 trace 的替代 |

分类：标签展开、严格 F<N、`1/2×K/4`、有限 Fubini 和阈值的有限最大值是可补齐的表达/省略推导。真正未供应的是 PP-W1-actual 的解析估计与实际 atlas-to-licensed-family 实例衔接；归一化价格和 relative-own-Θ 也不能在本轮静默标记已付。这不是根据一个 404 或源码索引缺名推断的数学缺口，也不是对原稿命题给出的反例。

原稿映射：`manuscript-body.tex` 256–356 给同 rho PP、factorial、真实物理尺度和 medium/long 路线；514–558 给正乘积命题及先用 `XS_N` 的证明；795–817 给正族 Θ、同 Q、alpha 与继承；819–855 给 W1/W2 原价；857–877 给前代选择及 430/441 共同细化。`own-chen-table-insertion-chain-20261009.tex` 129–175、222–244、253–355 给相同 ordinary/selected 支持与原母式。原稿固定提交为 `9731290e8f53cffda44129906cde6a965eaa869b`。

未执行 Lean/Lake/LSP、候选、helper、guard、fixture 或 artifact；本轮未执行 Git 命令、GH 命令或 GitHub 状态变更。仅四个已固定旧源码作小型 immutable GET，并核对先前记录的 blob；其余为本地源码/已冻结记录。旧 freeze 未变，h34、430/441、full PP、7/32 与 half/J6 范围均未提升。
