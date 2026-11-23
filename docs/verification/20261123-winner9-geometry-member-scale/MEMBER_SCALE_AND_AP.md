# 完整 Member 尺度与两号完整模数

原稿版本 `a988cba584d803ae2856a0de50efb582f4f3dd6a`。本批六份源码、十三条公开声明中，两个尺度模块的三条已通过编译、独立内核及完整声明审计；其余四个组合模块的十条仍为未编译源码。以下组合路线按这个状态阅读。

## 原同余窗口的两侧

稿本 `argument.tex` 第 23–39 行给出实际分子 $N$、完整 $x=UV$、$c_0x\le N\le x^{1+\kappa}$ 和四条严格不等式。一般命题允许 $0\le\kappa\le\sigma/100$。本次 Member 定理使用 `coefficient-appendix.tex` 第 252–281 行的实际应用范围 $0\le\kappa\le\sigma/200$，其中 $\sigma=\zeta/2000$。参数与矩阶的先后也见 `argument.tex` 第 189–199 行。

1. `eventually_complete_scale` 对固定 $c,C,\zeta,\kappa,\kappa_0$ 的较强几何窗口 $cN^{1-\kappa_0}\le x\le CN$ 建立双向放缩。该窗口来自 `coefficient-appendix.tex` 第 539–548 行。对 $x\le N$ 取 $y=x$，对 $x\ge N$ 取 $y=N$，始终 $q_y=\log_yN\ge1$，而 $x>N$ 处真正的 $\log_xN<1$ 得以保留。当 $N$ 足够大，$x\le CN\le N^{1+\zeta/16}$。这给出 $x^{1/3-\zeta/2}\le y^{1/3-(7\zeta/8)/2}$。
2. `eventually_residue_window` 直接以较弱的原同余窗口为输入。对所有 $0\le\kappa\le1/100$，由 $(1+\kappa)15/16\le1$ 推出 $N^{15/16}\le x\le N/c_0$。固定辅助参数 $1,1/16$ 只用于上一步。最后由原 $N\le x^{1+\kappa}$ 取回 $q_y\le1+\kappa$，阈值先于真实的 $\kappa,x$。调用者无需另外提供几何下界或 $x\le N$。这覆盖原应用的完整弱窗口，包括 $x=N$ 和 $x>N$。
3. `full_trim_medium_ranges` 在辅助 $y,\zeta'=7\zeta/8$ 上取原三项尚未消耗的单项式；在 $x$ 上还原真实 $U=A x^\zeta$、原 $\sigma$、真实附着 $M$ 与原 $N^{7/32}$。当 $M\le x^{\zeta/8}$ 时，第 2、3、4 个严格范围扣除实际需求 $8\sigma,15\sigma,15\sigma$ 后分别还剩 $371\zeta/1000,897\zeta/400,8051\zeta/3200$。第一项来自 $Q_1\le A<U x^{-\sigma}$。

## 同一个原 Member、词和真实矩形

`upper_member_all_complete_scales` 先固定 $n\ge111$、$0<\zeta\le\operatorname{radius}(\operatorname{collarIndex}(n))/8$、$\nu>0$，再取局部许可的 $0<\beta\le\min(1,\mathrm{floor}/\nu,\zeta/(16\nu))$。因此 $\rho=\nu\beta^2$ 在真实支撑下限内，$\ell=\nu\beta\le\zeta/16$，$M=N^\ell\le x^{\zeta/8}$。这里的 beta 只支付该有限政策的本地支撑和几何余量，所有 family 的共同密度、矩阶、对数精度仍需联合选取。

原 `rootFibre/rootHistory` 允许两根和任意实际有序历史，统一阈值在 $N$、根、同一物理 $Q=\mathrm{cellQ}(N,n,\mathrm{key}.1)$ 的 occurrence、模数之前。对避开原薄层、源为 enhanced 且上系数非零的成员，`upper_member_medium` 提供原有号值、$h=e d$ 和真实 rough 除子，再用 `presieved_upper_groups` 在所有 $\kappa,x,A$ 之前选出共同的原有序词 $v$ 和半开箱 $j$。上端点向量 $w$ 及 $D=N^{\lambda+\eta}$ 在所有这些矩形固定，`groups w D A` 可随实际容量 $A$ 变化。三个实际整数的乘积恒等于 $Bh$，其中 $B$ 是原历史的已读旧词积，$e$ 只进入第三组。$N B$ 出现在原 rough/beta 的允许素数筛上；同余分子与光谱项都是实际 $N$。

`active_chart_complete_integer` 在真正的 `chartTerm` 使用 `smoothTransition(s-1)`，非零性迫使完整整数 $b>N^{1-\kappa_0}$。`actual_member_HB_rectangles` 通过 `OriginalHBCompleteProductScale.exists_actual_HB_residue_threshold` 接入任取实际有序 HB 元素及其完整补积的右闭 dyadic owner。该中间接口仍接受任一合法 $A$。

`selected_HB_member` 量化每个有界秩的活动原 `Group` 的每一组真实非零有序 HB summand。两列由 `List.Forall₂ liveRow` 对齐。每个 `OriginalGroupTuple` 自带原 `factorTuples` 成员证书；`liveRow` 保留每次出现的原整数、原 HB 行号及其 `assignedWeight≠0`。逐元素产生的两侧 `Forall₂ Owns` 连同等式 `joined rows = pl ++ s :: pr` 出现在公开结论中，故相同 dyadic 标签或相同整数重复时，`left.length` 仍是原 `firstMedium` 的位置。这个位置的块给 $U=\mathrm{lower}(b)$，该具体因子词删除该位置后的完整补积给 $V=\mathrm{lower}(\mathrm{owner}(\prod(pl{+}{+}pr)))$。

使用原活动组的真实平滑支撑得 $\mathrm{chartN}/2^K\le X\le2^K\mathrm{chartN}$，用 `actual_occurrence_complete_window` 得 $x\le\mathrm{chartN}\le4x$。原有 `fixed_reserves` 和 `original_to_local_medium` 将 $X^{3\zeta}\le U\le X^{1/3+\zeta/4}$ 送到 $x^{2\zeta}\le U\le x^{1/3+\zeta/2}$，对应稿本 `coefficient-appendix.tex` 第 575–579 行。本次取 $A=U/x^\zeta$，公开结论同时给出 $Ax^\zeta=U$、$x/(Ax^\zeta)=V$、四条严格大小条件和每个真实整数分组与原 $N$ 互素。几何权仍需供给同一个 $C$ 使其非零处完整整数乘积至多 $CN$；稿本第 323–331 行规定原几何权支撑 product $O(N)$，第 505–515 行实施 trim。本声明在 `List ℕ` 的全部长度上写出该支持。原权若只在固定槽数 $k$ 上给出，则把其他长度的值延拓为零；在长度为 $k$ 的实际 tuple 上，原有号权、chartTerm 及其取值完全相同。这样需由最终具体几何权供给的，就是固定槽数上、对 HB 展开后实际使用的整数自变量成立的 $O(N)$ 支撑。任意未绑定的 $W$ 或只在素数点证明的上界，都不足以自动给出此项。

## 两号完整模数与精确均值

`whole_displayed_primitive` 由 `rootHistory_coherent.letters` 给旧词每个字母与 $N$ 互素，进而 $B\perp N$。上、下两号各自的 `actualSmallRoughModuli_coprime_target` 与 `actualLowerSmallRoughModuli_coprime_target` 给 $h\perp NB$。原每个 displayed $h$ 因此有 $Bh\perp N$、$h\perp B$、$Bh>0$ 和 $N\bmod Bh$ 属单位类，包括系数恰为零或 receiver fibre 为空的情形。`active_group_factors` 再由原权在 displayed support 外为零，推出两号的任何非零权及每个 $q_1q_2q_3=Bh$ 的三个原整数因子都与 $N$ 互素。选中 HB 矩形已对自己的三组实际调用此结论。

`signed_quotient_full_AP` 在两号共有的未筛 `chenQuotientPrimeSource N B` 上复用原 `currentChen_quotient_sum_supportedDivisorSum` 和其使用的 `chenQuotientPrimeSource_divisibility_fibre_card`。同一有号权逐项乘以模 $Bh$ 的 `chenPrimeAPCount − chenCentrePrimeAPCount`，并精确拆成原 `chenAdditivePrimeCarrier N` 上的互素均值 `finiteCoprimeMass/φ(Bh)` 与 `finitePrimitiveDiscrepancy` 的有号和。空纤维出现时仍按原均值记账。`exact_mean_on_every_displayed_modulus` 给每个 $Bh$ 的全部单位类 discrepancy 之和为零。实际固定剩余类 $N$ 上跨模数的有号消去仍需解析估计。

## 准确选源与已验证部分

逐个根的条数、当前状态、公开源与确切哈希见 [SOURCE_FILES.json](SOURCE_FILES.json)。全图为 1,039 个不同项目源、236 个外部源码边界，0 个未解析源；依赖源码已定位不表示这些模块已经全部编译。项目源身份按三片保存于 [S03_SOURCE_SELECTION.json](../../source-only/20261123-winner9-geometry-member-scale/S03_SOURCE_SELECTION.json) 引用的清单中。

集成选源在作者冻结版本上只复用一个已有已验祖先 `P4BSmoothGateUpperStep`，保持其原公开定义、声明和导入。六份本批源字节均未更动。两个小根的全部三条声明与公理见 [VERIFICATION_RESULTS.json](VERIFICATION_RESULTS.json)；四个组合模块不计入该验收。

## 剩余原合同

上号增强成员本次得到完整大小范围和逐因子互素性。把原有号系数分成 medium 命题需要的三个独立单有界系数序列、推原 Fourier/Mellin 模、给原 rough 槽的任意对数阶辅助互素 SW，并在同一完整 $Bh$ 上求真有号均值的解析误差，仍是稿本 `argument.tex` 第 41–68 行、`coefficient-appendix.tex` 第 581–604 行和第 491–502 行对应的工作。一般 lower、adopted/inherited/owner 正纤维、far rejected 的尖锐原许可、正域极限质量、共同 $\nu,\zeta,\beta$ 和依赖矩阶的账，以及两根实际 430 步与 11 个余项，仍须逐原 Member 与原价格收束。上一轮 $431$ 倍粗上界只支付粗载体量。上述有限恒等式也没有给出固定余数的跨模数 SW 或全正纤维相对误差。
