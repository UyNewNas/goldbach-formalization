# T20 独立数学源码复核 · Y26 原 W1/W2 异常

**限定通过。原 Y26 整行保留黄。** T19 在原 U3/U4 冻结根、实际选中 bank 的位置上，将半开窗精确换为严格 fresh 子计数，按三十六组原参数支付 selected collision，并把原根收据和被拒商数各自带符号送到同一 RootKey 的预算。尚欠真实 inherited 选择后的有向壳差和同一母族的估计。最强声明是 `owned_fibre_bank_receipt_budget`。它的左右两端都明确含有被拒商数。

## 原稿与适用族

原稿 **9731290e8f53cffda44129906cde6a965eaa869b** 的 `manuscript-body.tex` 795–817、830–855、857–877 要求同一物理 Q、非负外层标记、原父 Θ、全部 full/selected squares、ceiling、真实 α 及零质量绝对误差。配套 `own-chen-table-insertion-chain-20261009.tex` 147–166、269–353、388–398 给出各动作原 cutoff、增强/经典分支及 U3/U4 重叠系数。独立从 **3d15576a2eb00ba03deb3cf54f170c0a7f91c1f9** 的 Git 对象核对 S17 字典、历史粗糙度、原始双素数和各母项，另从历史对象逐项检查 `selectedLevel` 与 `requested_bank_tests`。T11 的 REPORT/REGISTRY 是入口索引。

这里的一个位置是原 `resolve/Selected` 选定 106 个 bank 槽中某槽的 `LevelIndex`。假设为偶数 N 足够大、0≤τ≤1/12、1/(n+1)≤11/384、p 属于带标签 rt 的原素数带、g∈Fin 430。碰撞阈值先于 N、精度、根、p、位置和 bank；纤维汇总结论还统一于根码 m,c。每固定 rt,c，先取 `rootFibre`，由真实归属式取得 Q=cellQ N n c.1，再相加。重叠同一 p 的 U3/U4 各有自己的标签，逐席次使用 levelMark，不将不同 Q 汇作一个 Θ。父计数是按请求处当前一代的 physicalDefect，普通子项读前代，固定项与根取权层次保持原样。

## 三笔核算

1. **端点与前缀 repeat。** S17 的 W1 字典取 dN 掩码，W2 三个 singleton 及四个 pair 取 N 掩码。对这里特定的冻结网格，Q=N^(u/v)，v>0。正有理下端点 e/f 若落在 q 上，则 (Q/d)^e=q^f；提升至 v 并交叉相乘得 q∣N^(ue)，与原窗的 q∤N 矛盾。W2 两坐标分别应用原有的 `actual_half_iff_open`，保留严格仿射平方门限。对 selected W2，原父在自身 cutoff 粗糙，选中动作的 target≥父 argument，所以每个 d 的素因子 ≥ cutoff(Q,d,target)。母窗的每个字母严格小于该上界，故恢复窗内的 q∣d 无点；pair 的两个坐标均如此。W1、W2 原下墙在这个确定的族上均有算术排除证明。任意实 Q 的半开端点仍按 S17 留账。两素数保留 small<large，继承的物理 word 追加 [large,small]，Gamma5+/6 读固定 A、Gamma7/8 读 small，对应原 rho；未改写 switched 的 α 或 rho。
2. **Selected collision。** 对真长词 w，事件在原 additive-prime receiver 上，存在素数 r，r∣prod(take(|w|−2,w))、r 在原 cutoff 以下、r∣(N−ℓ)/(d·prod w)，兼有原 source 谓词。长度二时首积为 1，所以这两个槽没有此事件；长词与 old-repeat 的提升交也为空，理由是该词每个字母均在同一严格上界以下。核对原生 `FourthRowMotherBadPrime.lean` 12–21，三个恢复费用正是 N 窗上 q∣d 的计数求和。余下长词 collision 仍按自身原字、重数及 d·prod w 逐项计费。原 `collisionSwitched_le` 的五个端点可自由指定。`rootHistory_support` 给 L≥L*，`history_integer_roughness` 给所有旧素因子 ≥N^η，η=L*/6>0；全 36 行 s0≤5、Q≤N，因此 A≥N^η、Z≤N。统一上界是 22(1+log N)^6 N/(η d N^η)。用同一母 Θ 的单原子下界 2 C* N/(d log²N)，一次统一阈值可付 εθ。这里的单原子比较只估计稀疏整数异常，普通 sifted count 的分布估计仍在带标记族上使用。
3. **106 槽及原收据。** `selected_debt_exact` 在 W1 原 lower debt 的 /2 以及 W2 三 singleton、四 pair 的 /5 上重写，W2 原 rowDebt 正好多出一次 collision/5。拒绝的 pair、其余正词、固定项、W1 prime restriction、W2 的 ordinaryBase−baseValue 和严格前代差额均有显式账户。对每个位置分别给母式 ε/2 和碰撞 5ε/2，然后乘非负 levelMark 相加，得到 ε·actualBankTheta。该 Θ 是相同 Q 的原 4 li(N) C(dN)/(φ(d)log(Q/d)) 乘原路径标记之和；没有除以 Θ。空 bank 或零权的异常预算直接为零。某位置原收据纤维空而父的 Θ 仍可正，连续近边界盒的绝对误差也未由此支付。

T17 确切依赖 `Part5OriginalH430OriginalReceiptMemberPullback.lean` 的 `rootMasked_count`、`member_product` 与 `actual_member_count_split`。在每个严格子边，真实 B=pD，给同一 ℓ 的两个商为 x=(N−ℓ)/B 和 Dx=(N−ℓ)/p。子 cutoff z 粗糙的 x 仍须分别检验 D 和 x 在原 A₀=N^a 处粗糙。根收据拉回、被拒商和原 full quotient 形成精确分拆，单子计数在 debt 里是负项，双素数计数是正项。若 D 有一个低于 A₀ 的素因子，则该位置与原收据的交为空，其 raw count 全部落入 rejectedChild。保留原 cutoff 和父 Θ 的 `full_bank_receipt_shell_budget` 与 `owned_fibre_bank_receipt_budget` 导出的就是这个带符号、逐实际位置的账式。该分拆不产生被拒正项的衰减。

## 整行仍欠

- 证明原选中族的 parent/child rejected shell 在所需方向得到付款、抵消，或提供求和后直接适用于同一 inherited 母族的 sharp 估计。一个可自由选择的 receiver E 可代入精确等式，未给该 E 上的母不等式。普通和 switched 剩余项须依其明确的作用域认领。
- `selected_child_gates` 传递给定的真实物理根 full/selected 两门。增强分支已有按根的辅助界；`ell_aux`、原 tent 和较低的 frozen total 是不同量。所有原始标记父、near-cap/equality 面的共同缓冲与外层真实质量仍须另证。这里的正 L* 来自已生成有界历史，不能移作任意正残差族的一致界。经典分支另有其原适用条件。
- 本许可不延伸至完整 Y25、原 Y26、八供应者、h34、H247、采用种子或全 430+11 共同细化。静态数学源码复核，正式信用 0，未运行本地 Lean/Lake/LSP、stage/guard、数值 producer/证书或 CI。均未编辑作者源、原 continuation、main 或任何 Git/远端状态。

最终重新核对了 T19 三源全部 32 条公开声明行、实际导入、五件作者产物的字节和冻结 SHA。作者登记的两份原稿、25 项证明源和两份固定提交的 native 源均以原始字节核对 SHA-256、Git blob。

`ALLOWLIST.json` 给出本次允许的精确源字节、SHA-256、Git blob 标识、所用原稿及关键历史对象。
