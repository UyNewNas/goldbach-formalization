# T17 / Y25 — U3、U4 原收据在真实 Member 路径上的精确回拉

**冻结结论：真实根入口、每条已生成普通历史的原收据交集、增强分支逐点严格平方许可，以及选中 bank 盒的正标记/Θ 字典，已给出五份候选 Lean 源。全 Y25 与 h34 仍开放。** 未运行 Lean、Lake、LSP、stage、guard、数值 producer/证书或 CI；没有修改 continuation、Git 引用、main 或远端。没有编译、传递公理或内核验收，formal credit = 0。T18 独审决定独立登记。

## 原稿与对象

以原稿 `9731290e8f53cffda44129906cde6a965eaa869b` 的 manuscript-body 795–817、857–877、887–892，以及 own-chen-table-insertion-chain 129–175、222–244、253–355、388–403 为准。前者要求正的外层标记、同一 Q 和真 α；后者区分增强与经典根，要求保留原指定素数、有标记的槽、完整平方/selected-remaining 平方、祖先物理上界，以及半开原窗。原稿没有规定从每一个原根收据中选择唯一一条深 430 的赢者路径；也没有给出“每层普通后代都还通过原根筛限”的断言。

本次读取只读 sourcehead `3d15576a2eb00ba03deb3cf54f170c0a7f91c1f9` 与旧 h34 分支 `001d139e667eb5cb42f1e9ca8f02de221b00db5c` 的冻结依赖。提供的 OwnedRootCounts、HistoryQuotientCounts SHA256 均已逐字节核对。T11 盘点、S28 整体 HOLD、R14/15/16、S17 以及旧 RequestedMember、FullTaggedActualFinPushforward 等有用的精确版本见 REGISTRY.json（32 个依赖/复用条目）。未重做 T07 的经典分布/Γ9–21、T08 的 H247 或已有 bank floor/Buchstab 恒等式。R14 的 Member 路径与 R16 的 parentTheta 被实际调用；R15 的 native-x 权/换元和 S17 的端点/repeat 分解保持其原有范围，此处不把它们当成本次算术许可。

## 1. 唯一的整数映射不是把根商和子商取成同一个数

固定实际原标签 k、原素数 p、其真实 emitted list position o。令 B 为 o.current.old 的乘积。由真实 Member realization 和 integerWord_prefix，原词从 [p] 起，故 B = pD，**D 是该整数词的 tail.prod**，正性来自真实 parentWindow。若加性素数为 ell，后代商为 x，则

    N − ell = Bx = p(Dx),     q_root = Dx,     x = q_root / D.

这里 q_root 和 x 是商，均不假定为素数；ell 是原加性素数，沿这次换元完全不变。乘 D 仅在固定 occurrence 内单射，不对不同路径或来源标签宣称单射。写 A=N^a，z 为该真实节点本身的物理截断，R_y(m) 表示每个 m 的素因子至少 y。两个独立定义的集合精确对应：

    原边：q ∈ originalReceiver(N,p)，D | q，R_z(q/D)；
    子边：x ∈ chenSiftedQuotientPrimeSource(N,B,z)，R_A(D)，R_A(x)。

前后双向的原因是原根门 R_A(Dx) 当且仅当 R_A(D) 且 R_A(x)，不要求平方自由、不排除 q=1，并保留等于截断的边界。实现见 OriginalReceiptMemberPullback 的 `originalReceiptLane_image`、`originalReceiptLane_test`、`owned_member_receipt_pullback`。因此若 D 有一个低于 A 的素因子，该交集为空；这不意味着原 ordinary 后代计数为零，也不意味着其 Θ 为零。

同一原加性素数上的实际遮罩是

    rootMask(N,p,ell) = ell.Coprime N ∧ R_A((N−ell)/p).

`rootMasked_count` 从原 frozenCarrier 的整除和原 prime labels 推得其精确为上述子边基数；`owned_member_masked_count` 将其拉回原边。根的实际起点 D=1、冻结物理截断 z≤A，故原边恰为全 originalReceiver；`original_U34_masked_origins` 对原 root fibre 和双标签求和恢复原 currentChenUpsilon3 + currentChenUpsilon4。它不是把根单位标记猜成后代收据数。反向看，`actual_member_count_split` 把**未加这层新遮罩的真实 frozenCount** 分成原根兼容收据和 rejectedChild 的基数，后者是实际剩余商的集合差，不是抽象正部或被宣称已付的误差。

## 2. 增强根逐 occurrence 的严格平方/物理许可

原 U4 恒属增强，U3 在 x=log_N p<57/224 才属增强；等号入经典尾，不能要求其物理根通过 2x<λ。旧 `enhanced_frozen_descendant_buffered_cover` 留有输入 frozen λ<v(x)。这里从 p.Prime、p.Coprime N 和冻结 λ 的自然有理网格表示 u/b 推出严格不等式。若 x b'=m（b'>0），则 p^{b'}=N^m，与 p∤N 矛盾。在 v 的两条实际直线 (1+x)/2、57/64−3x/2 上，λ=v(x) 分别强制

    x b = 2u−b,       或       x(96b) = 57b−64u.

两侧差的非负性由 x>0 得出。这排除了相等，而 frozenLevel_bounds 已给出 ≤。令 C0=(max(λ,2x)+v(x))/2，C1=(C0+v(x))/2。原 Q13 与真实 `rootHistory_member` 给出 C0 上的同一完整平方列表和同一 selected/remaining 列表；逐项由 ≤C0 推得 <C1。新的 `enhanced_actual_member_strict_cover` 同时给 λ<C1<v(x) 与 N^{该 occurrence 总层}=原 rootQ。没有在较低的物理 λ 上虚构增强根平方。C1 是**逐实际素数的辅助分析 cover**，不是对所有 N 共用的正裕量或新的筛层。

物理 ceiling 本身从既有 `rootHistory_coherent` 的 cutoff_fits、`history_ceiling_le_letter`、`child_admission`、`requested_bank_tests` 取得；原 selectedWord 始终是根槽 [log_N p]，pair 按 [large,small] 追加。祖先槽只会追加，由 `replay_slots_prefix`、`replay_ancestor_filter`、原图 `realize_ancestor_choice` 保持已选 cap 的输入。真实 α≥2 与 Q=B N^L 来自 `rootHistory_support`，不是假设。经典 U3 只保留已有 `classical_frozen_descendant_level`（τ>0 时 λ≤1/2−τ），不混入增强平方或新 BV 支付。

## 3. 正 Prime-box、不可变 owner、重数与 Θ

`atBox` 从真实列表位置计算有限 Program（有序动作、所有物理盒槽）、是否结构性夹在 2、原分支以及实际查询 owner。最外层用原 rootKey 决定根 owner 和共同 Q=cellQ；从不挑代表素数当作整盒 Q。对指定的 g+1 层和 106 的某个赢家动作读取原 `selectedLevel`；`occupied_member_owner` 用实际 resolver 和整数路径给出 Member 与唯一请求的 owner（公共端点可能同时属于两个闭 cell，但请求只指定其中一个）。每个位置的 sigma 为真实原边系数乘积：retain/BH/W1 fixed=1、W1 singleton=1/2、W2 fixed=4/5 或 1/5，其余 W2 子项=1/5。正性为旧 mark_pos。

`U34_box_original_receipts` 精确回到两套原 (p,q,tag) 集合：每个原 q 在本盒的系数是所有满足 D|q 及 R_z(q/D) 的原列表位置的正标记之和 `receiptMark`，不是 1。一个根收据没有匹配时此和为零，多条匹配全部相加。U4 重叠区在 U3 和 U4 均保留，不假设两个标签使用相同 Q、深度或路径。

在同一批位置上，`sum_boxTheta`、`U34_selected_theta_exact` 把原逐位置 **levelMark × thetaAtom(N,Q,B)** 准确拉回到同一盒的 parentTheta；`boxTheta_nonneg` 的 Q/B>1 与 B>0 来自真实位置。Theta 是前缀族的正规化，不乘以收据基数，也不因个别位置的 rootMask 无收据而删除。

一个盒的实际 s 可变。`fixed_query_original_receipts` 给出精确同 Q/同 s 的原 markedPhi：结构夹在 2 的盒固定取 2，其余占用盒取其 owner 的闭 cell 右端 w≥s。降低物理截断 z(w)≤z(s) 后，用原 frozen_selected_buchstab：

    共同 w 下的 markedPhi（原 rootMask）
      = 以 receiptMark 计的原根收据
        + 实际 [z(w),z(s)) 中最小素因子的正 shell。

每个 shell 子项带原 B*r、原加性素数遮罩和原位置 mark；未对 shell 求小量，也不把直径至多一格的移动当成可忽略。全层版本 `all_emitted_original_receipts_plus_rejected` 对 G=0,…,430 的**每一层分别**精确分解：G=0 为 seed；G>0 按相应 iterate(G−1) 的实际 retained、Buchstab、106 bank 或 exterior 分组。它保留每个位置的 rejectedChild；exterior 的表读数 0 不令算术计数为 0。不同时相加不同代，也不以任意 inspected depth 的正部作为定理输入。

## 剩余缺口与移交

* **I（形式表达）**：五个候选模块及登记的旧跨分支 imports 尚未在固定 Lean、mathlib 和 native 源下分层安装、编译或接受传递公理审计。这里的检查只有原始文本、源码接口和 SHA。不能给 kernel/green 信用。
* **II（已补算术/几何省略）**：原收据在每条真实 emitted Member 上的双向原像、原根 fibration 起点、实际源遮罩、两标签重数、按盒正 Θ 的拉回、真实增强根逐点缓冲与两套严格平方。这些结果不以 h/H、paid count licence 或外加 common Q 为输入。
* **III（实质未给）**：rootMask 是原根收据与后代普通族的**交集**；普通 sieving 时更换 cutoff，会产生本包明示的真实新收据。原稿对后代的表估计是正 marked family 的平均估计，不是允许对任意收据子族沿用同一 θ 主项。需按原动作给出完整普通/转换项的算术所有权与符号，付或相消不兼容收据、半开端点、旧前缀 repeat 和 fixedQuery shell；不能把这些全删去，也不能拿逐根 C1 当作 pre-N common margin。恢复全部 modified-weight/selected-subproduct 分解、统一 positive prime-box 估计、same-ρ switched PP 与 430+11 仍开放。旧 rank-two 真 Fin 的全部 tagged receipts 与这里的 ordinary feedback 位点/系数也不是自动相同的对象。未证明稿错。

交接给 T19 的公共接口是 `rootMasked_count`；其新 singleton/pair 需自己证明实际乘积和物理粗糙性。给 T23 的是根 p/旧词 tail 整数型关系；catalog 中的任意几何 Member 不能倒称为已生成算术收据。**T18 已对 REGISTRY.json 的五个源码 SHA 签署 SCOPED_SOURCE_REVIEW_PASS；全 Y25 HOLD。** 独审文件：同级 t18-u34-review/REVIEW.md、ALLOWLIST.json，哈希登记在本目录 REGISTRY.json。
