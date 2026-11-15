# T08 W1 price lower：独立精确源数学复核

结论：**AL+，仅限下列精确源码中两条定理的数学方向、原对象适用性及可见 public 声明审查。** 没有发现实质反例、方向错误或新增目标形前提。状态仍为 **SOURCE_ONLY / UNCOMPILED / ready_to_install=false / formal credit=0**。本结论不是 Lean 语法、API elaboration、递归 import 闭包、安装选本或编译通过证明，不改变 P5/h34 原有 HOLD。

复核者：独立于作者的 U03，按 ROOT 指定 Astra/xhigh；日期 2026-11-15。只处理这一新候选，不重审全部旧图。原 T06/P1 审查目录、作者目录、旧 freeze、主稿状态均未修改。

## 1. 精确对象与身份

- 候选：`output/resume-20261115/t08/w1-price-lower/Part5OriginalH430W1PriceLower.lean`，3498 bytes，76 行，SHA256 `09a535f1efe9685e4a99cc3860b83fd5e8d375850e28cca1d1025b06e0cf85ae`，按实际字节计算 Git blob `65da19f7bd23ca4f6dc6d89fd9f779d9bdcc1184`。新源没有在本审查中获得 remote pin。
- 作者 `FREEZE.json`：4431 bytes，SHA256 `355cf9ec1367456340b02debf20775b1230c0e01598ee049312f783637b9ebb4`。
- 核对三件被 freeze 列出的 artifact、12 件依赖快照、7 件先前 freeze/source 身份，全部匹配；其中 10 件 Lean 依赖原字节保存在本审查 `sources/`。另外为原 carrier、RootKey 和 currentK 核对 5 件本地定义，保存在 `ADDITIONAL_SOURCE_IDENTITIES.json` 及同一 `sources/`。
- 主稿 `chen-imbalanced-semiprimes/paper/source/manuscript-body.tex`：68191 bytes，SHA256 `ee6aecc164cc59f2d1fed1ad9e48f18f98472ab1d77ab425d53d93bc41ce56bd`。

精确记录见 `IDENTITY_AUDIT.json`。上述 byte/hash 对照只复用已有本地源及先前身份记录，没有新的 Git/ref/远端存在性审计。15 件源副本不是递归依赖闭包。

## 2. 两条声明的数学核对

记 `li₀` 为 `AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418.logarithmicIntegral`，`C` 为 `Wu2008DoubleSieve.wuSingularSeries`，`v(N,d)=thetaConversion N d`。

第一条 `ImbalancedChen.Part5OriginalH430W1PriceLower.thetaConversion_lower`（候选 25–62）仅要求自然数 `N≥4`、`d>0`，结论为

\[
 b_N:=4li_0(N)C(N)/N\le v(N,d)
 =4li_0(N)dC(dN)/(N\varphi(d)).
\]

等式右端确为 `P2EnhancedSwitchedTrueNormalization.lean:98–101` 的原定义。物理目标、li 自变量和分母仍是 **N**；`dN` 只处在原 singular factor 中。没有将目标改成 `dN`，也没有把 `C_N` 换成 `2C_N`。`Normalization.lean:55–69` 的奇素数积与原稿 6–12 行的 `C_N` 一致。

证明逐步成立：`N≥4` 给 `N>0`、`log N>0`；`BoxMassTheta.lean:31–40` 的 `box_trueLi_lower` 给 `N/(2 log N)≤li₀(N)`，因此 `li₀(N)≥0`。`Normalization.wuSingularSeries_pos` 给 `C(N)>0`；`Omega3XNormalization.lean:36–38` 的 public `Wu2008DoubleSieve.wuSingularSeries_le_mul` 给 `C(N)≤C(dN)`，仅需 `N,d>0`，没有偶数或互素前提。配合 `0<φ(d)≤d`：

\[
 C(N)\varphi(d)\le C(N)d\le C(dN)d,
 \qquad C(N)\le dC(dN)/\varphi(d).
\]

最后乘非负的 `4li₀(N)/N`。代码没有除以质量、li、C 或缺陷量。`d=1` 时两边精确相等，是系数及方向的独立边界核查；无隐藏的 `d>1` 条件。

第二条 `integerMass_price_lower`（65–73）对同一 `N,d` 以及任意实数 Q、`i : Fin 7`、`j : Fin 10`，将同一个原 `integerMass N Q d i j` 乘在两边。非负性在证明内由自然数基数的实数强制转换及有限和得到，没有添加质量非负、非空、正总质量或目标下界前提。空窗口、空和、质量为零均包括。

源码中的特殊算术名称在所读源里为 public 声明，不依赖 private lemma 导出补丁；`thetaConversion`、`integerMass` 也是公开定义。常规 totient/order/cast/tactic 调用仅做源阅读与数学解释，未运行 Lean，不能据此声称当前安装环境已解析这些 API。作者三个 direct imports 与身份记录相符。

## 3. li 的常数不能偷换

`P2MarkedThetaLiNormalization.lean:39–43` 精确写出

\[
 \operatorname{trueLogarithmicIntegral}(x)=li_0(x)+2/\log 2.
\]

旧 `thetaConversion` 注释虽有 “true li” 字样，实际标识符是 literal `logarithmicIntegral`；`box_trueLi_lower` 的实际结论也使用这个 literal 标识符。候选两条声明与证明均沿用 `li₀`，没有增加常数。若单独把左边换成 trueLogarithmicIntegral，`d=1` 已构成反例：左边会严格增大，右边原价不变。本 AL+ 不允许这种替换，也不授予 literal/true 的相对误差归一化结论。

## 4. 原 family、unit、重复因子与根 Q

原 `Part5OriginalH430W1PhysicalRoughDictionary.lean:16–18` 为

\[
 a_{N,Q,d,i,j}=\sum_{(a_1,a_2,a_3)\in\mathrm{orderedTriples}(\mathrm{primeWindow}(dN,z,w))}
 \#\mathrm{roughNumbers}\!\left(\frac{N}{da_1a_2a_3},a_2\right),
\]

其中 `z=cutoff Q d (W1Anchor j)`、`w=cutoff Q d (W1Target i)`。候选没有复制或改定义，只调用这一对象。

- `FiniteWeights.lean:21–22` 保持 `a₁<a₂<a₃`；不是新引入允许重复的外部三元组。
- `GoldbachWeights.lean:21–26` 的原窗口保留素性、与 `dN` 互素、下端闭/上端开。
- `LiLiuPrereqBuchstabCount.lean:20–26,30–53` 的 rough integer 只要求正整数、`r≤N/(da₁a₂a₃)` 以及所有素因子≥`a₂`。它没有 squarefree/prime 条件，重复素因子、与外部因子重合的许可情形均保留；`r=1` 恰在上界≥1 时保留。没有把 unit 从质量删掉。
- `Part5OriginalH430BankAfterW1PrimeRestriction.lean:30–62` 的 prime restriction 是同一 rough carrier 再加原 `chenQuotientPrimeSource N (da₁a₂a₃)` 过滤；候选没有用这个较小载体替换 unsifted 质量。

真实 `d` 的来源是 `SeedHistoryMass.lean:24–25` 的原 occurrence 的 `parentProduct ...current.old`。public `scale_and_alpha:31–38` 对原 `LevelIndex` 同时给 `d>0`、原 `Q=rootQ ...`、`Q=dN^L`、正残余尺度以及 `trueAlpha N Q d≥2`。因此使用新比较时不需新加一次正性许可。原 `all70_rough_bound:89–96` 已在所有 `N,Q,L,d,i,j` 之前给共同 `T≥4`；`N≥T` 足以提供这里的 `N≥4`。新比较自身对全部 Q,d,i,j 同时成立，不产生随标签选择的 N 阈值。

`OwnedRootCounts.lean:33–43` 的 RootKey 保留 Q code、实际 scalar owner、clamp 和辅助精度；`original_fibre_geometry:90–101` 只在原 fibre 上证明 `cellQ N n c.1=rootQ N n k t p`。候选对任意 Q 成立，故可逐项在每个根的 **own Q** 使用；它没有声明不同 RootKey 的 Q 相同，也没有重新分配 owner。`trueAlpha=log(N/d)/log(Q/d)` 保持原值；这里的标量比较无需 alpha 前提，不表示后续 envelope 可以省掉原 `alpha≥2` 门槛或把 alpha 重置成 2。与原稿 808–817 行一致。

原位置权与重数也没有被消去：`SeedHistoryMass.lean:63–76` 保留 `levelMark` 的逐位置求和，`groupedSigma` 用 fibre sum 保留相同 d 的多次出现；92–95 行从原 mark 正性给非负权。候选不直接涉及 sigma 或聚合定理；仅可在后续使用已有非负权作有限加权求和。不能把这一点表述成候选已经完成 RootKey 聚合、same-rho consumer 或 signed outer sum。

## 5. 四、四分一、二分一和剩余价格方向

原稿 795–806 行的 normalizer 是 `4 li(N)` 乘原非负 marked family 的均值，且只在一族内部取共同 Q；并非逐 B 分布估计或 signed 外测度。新声明保留这个 4。

原 `BankAfterW1PrimeRestriction.lean:64–66` 为

\[
 \mathrm{cleanDebt}=\bigl(T-(K/4)va\bigr)/2,
\]

这里 `K=currentK=8452171/1250000>0`（`W1OriginalBaseEnclosure.lean:23`），不是更换成其他 seed 的 K。由 `b_Na≤va`，得到正确的上界方向

\[
 \mathrm{cleanDebt}\le\bigl(T-Kli_0(N)C(N)a/N\bigr)/2.
\]

在原式展开时系数是 `K/8` 乘 `va`；不能丢掉外层 `/2`，也不能在消去 `v` 的 4 后仍错留一个 `/4`。作者报告的未付价格余量公式

\[
 XS_{\rho,N}-(K/4)M\le X\bigl(S_{\rho,N}-Kli_0(N)C(N)/N\bigr)
\]

在同一实际非负位置族 `X=Σσ_la_l`、`M=Σσ_lv_la_l` 下代数方向正确。报告明确未写聚合 consumer。原稿 830 行的 `KI/8` 还涉及原 switched integral 的连接，本候选没有独立实现这一整项或支付 cleanDebt。

## 6. AL+ 边界与保留 HOLD

这个局部价格比较是原归一化中可由已有 singular monotonicity、totient 界和 literal-li 非负性补齐的初等省略；源数学没有新增困难的分析命题。其表达方式保留原实际对象，不是以 desired-price/desired-support/PP 为假设的重述。

以下仍 **HOLD**，本 AL+ 不给任何连带完成信用：

1. 原稿 507–512、529–559 行要求的同一物理 `rho_N` 的 majorant、density 与 full PP；对实际标签族的 signed Δ 及绝对误差；J=0 时仍须绝对估计。
2. 把 `S_{rho,N}-Kli₀(N)C(N)/N` 的加权价格余量控制为所需小量。这里只用 li 非负；粗界 `li₀≥N/(2log N)` 不足以给系数 1 的渐近支付。
3. 原 RootKey/own-Q 的完整非负聚合与 relative Θ 误差、实际 W1 discrepancy、h34、4.30/4.41、430 次迭代的全部未付接口。不能把 `all70_rough_bound` 的上界倒用成下界，不能把 J 的 limsup upper 替换实际 X 进入有符号价格抵消。
4. 原 root receipt 仍是 `if old=[p] then originalReceiver else ∅`；receiver 可空。ordinary append 仍是整笔 rejectedChild，不能因本价格比较把 ordinary 质量判零。原 occurrence、E/Q/old、owner 与所有位置不变。
5. 可安装 source selection、全部递归 imports、Lean elaboration/API/compiled pass。`Omega3XNormalization` 已读的是固定 `09b97db5764ade1246bfb77206baa1b124760958` 的 research-path 旧本地 body，4732 bytes / SHA256 `2b5987599c216e2637630d21852b88f6afc0d454238cec3d86d9ea804b1260cb` / blob `3aed415b95f4c387cb12790ee0c5e13ceedbc1e6`。其 monotonicity 正文与本证明匹配；先前标记仍是 transitive locator candidate，不升级为 owner-selected/install-ready pin，不覆盖 T04 root pin。未闭合递归 cone 不否定这两条局部数学论证，也不能凭局部论证宣称递归闭合。

本轮只读既有 source/text/JSON，计算 byte/SHA/blob，写入本审查目录。未运行 Lean、Lake、LSP、候选、guard、setup、fixture 或证明 helper；未运行 Git/GH 命令、未知对象探针、promisor fetch、下载、额度查询或再派 agent。最终字节复核记录见 `FINAL_STATIC_READBACK.json`。
