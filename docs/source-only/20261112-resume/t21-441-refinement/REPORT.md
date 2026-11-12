# T21 / Y28 · 原 430 回放与十一根发生的共同细分

**冻结结论：已构造一个可在所有原读取上使用的有限正光滑分片；已在实际 U3/U4 发出路径上绑定原查询、祖先投影、原账及选中 Buchstab 严格子行的共同阈值。尚无覆盖全部十一项后续、各 W1/W2 子行与普通/换结基项的原计数共同 realization。Y28、Y29、h34/hLower 均保留 HOLD。** 本包含八份未编译 Lean 候选及一份数学说明，仅作 source-only；形式信用为 0。

母本是 9731290e8f53cffda44129906cde6a965eaa869b 的 manuscript-body 795–895、global-chen-lower-completion §§3–4 及 own-chen-table-insertion-chain。原文 857–877 规定上一代和 closed support minima，只有 U3/U4 用重新播种的 430 表；其余指定位置保留 H248。878–895 的十一项是带原系数的**并列根/叶发生**，不是 H430 完毕后沿每条路径再顺次更新十一遍。441 是原证明允许的传播层数上界。冻结代码读取 3d15576a2eb00ba03deb3cf54f170c0a7f91c1f9，以及 T11/S28 之后另定位的独立 P5 历史提交 001d139e667eb5cb42f1e9ca8f02de221b00db5c；输入路径、Git blobs 和原始 bytes SHA256 列在 REGISTRY。S28 的 FINAL_CHECKPOINT_WHOLE_SCOPE_HOLD 保留。

## 实现及接口

| 源码（文件名省略固定开头 Part5Original） | 独立可核对的结果 |
|---|---|
| CausalSmoothAtlas | 真实光滑一维 label 与联合乘积分片；端点 0、1 在平台上；任意有限精度 overlay，每个因子按其树地址精确边缘化。任何指定物理分辨率都可在 N 前达到。 |
| H430JointQueryEnclosure | 在真实本原坐标计算完整 R14 QueryMember；在同一批非负光滑函数上由 hit/sure 系数构造上/下函数，逐点夹逼，差恰等于 mixed 质量。未用“叫作等号所以无质量”。 |
| H430SmoothPrefixRequests | 从真实 ChosenPath 的 old word、追加字母求 chronological 的任一祖先边缘和；position_certificate 包含真实 Member、rootQ、前代来源与原 mark。各代选中 baseValue、Q80 floor loss、带符号 (Θ−1)·read correction 总和精确恢复。 |
| H430EmittedNativeQueries | 由真实 root+path 构造本原 tuple：原双槽为（小，大），原 old word 追加（大，小）；nativeCoordinates 与 nativeProgram 精确绑定原整数解释器。emitted_native_prefix_marginal 在**同一物理坐标顺序**保留所有较早槽。emitted_owned_iff 为原 keyAt 的四个字段、固定 Program、mode、owner、winner 与 terminal atom 的联合查询；不把全几何 catalog 当实际计数。 |
| ElevenSmoothRootDisintegration | 在原 p5MarkedElevenSource N E 上分解，每个有标记 token 仍含同一加法素数、原 tuple、同一 E、原整数重数。两种普通 start 为零个根素数，其他各行用 1、2、4 个实际槽；quarter_weight 对十一项逐项恢复原系数，actual_quarter_root 精确给 currentChenPairedPrimeSum/4。U3/U4 的原 [p] 与 rootRequest.old 一致。 |
| H430RefinedFeedbackBudget | 对每个真实被选请求，在同一非负 native parent mask 下复用 106-bank 与两向 Buchstab 的**原整行** absolute gap；原行质量 ≤12Θ、Buchstab ≤5Θ，零 Θ 不作除法；retained 指定旧 cell，exterior 的表读数为零且不生成边，原收据、计数与 Θ 不因此置零。native_base_floor_theta 给同一 tuple 上的原 base/floor/带符号 Θ correction。 |
| H430ChildSmoothPrimeTests | childTest 用物理 Lu；compact_uniform_sandwich 在 (L,c) 紧集上一次选择 N。两向 Buchstab、401 原子含 knots 与所有新增标签的**绝对误差和**受 δ 控制；这里的 trueSingleTest 仍是 N-window。 |
| H430StrictChildBuchstab | 将上一条真正送回 primeWindow(dN)、closedChildren 与 strict singleChildren，使用原 ceiling 等号纤维的 4/A 界。all_strict_requested 对每个 coherent+selected 前代、真实 Q/χ/d、两方向、全部 401 原子和全部新增标签，先绝对值再乘真实旧数组系数相加，≤δ·θ_parent。reserve_common 构造同一个 N₀，覆盖该严格子行与 FeedbackAt 的范围。 |

完整推导、精度顺序及 absolute/relative 区别见 [CONSTRUCTION.md](CONSTRUCTION.md)。当前最强定量终端不是“假定一个共同阈值”：先由 P5RenewalFiniteError.exists_local_reserve 选 δ 满足 (7/2)δ(12^441−1)/11<reserve，选共同细网格；实际 mother 的 T 由两个原一致请求定理生成，Buchstab 新槽的 T 由原紧参数、删除、ceiling 定理及固定有限索引生成，才取两者最大。任意更细、已经固定的计划也可用 all_strict_requested **重新产生它自己的** T。未在随 N 改变的 LevelIndex 上取最大，未重算数组或 producer 证书。12 是传播预算的上界；7/2=14/4 来自真实十一项，绝非接上未除 4 的整数账。

在固定 U3/U4 几何图上再用 T23 的全几何 Θ 字典及完整 native proper/equality 分析，可取一个精度和一个 N_geom，使全部固定 root/Program/mode/winner/atom 的混合盒**绝对**成本同时小；证明及位置重数界见 CONSTRUCTION。此结论是书面综合，不是第九个已形式化的 Lean 终端。实际发生中，同一子分片的父权只被用一次：Buchstab 的新精细估计可代替旧整行估计；若两种不同误差要相加，先在 δ 中分额。source equality 不等于分析费用已小。

## 十一项和八个供应者的接缝

| 原位置 | 已接地点 | 不能由这个等式自动获得的付款 |
|---|---|---|
| L1,L2 | 原 indicator start / additive prime，一致的零根槽与旧值恢复 | 后续普通 causal subtree、极小末素数尾、逐前缀 cap retest 的计数与有向余额；L2 原 H248 最小素数项已删除。 |
| U3,U4 | 同一原根 [p]，同一 Q 的真实 430 seed-only 读取及 native owner；严格 Buchstab child 见上 | 430 induction 所有 original receipts/adopted seed/base 的有向比较，尤其新分片下 W1/W2 各新子测试与 swapped costs。 |
| L5,L6 | 原两个素数与共享 E 所在原行，正标记类型和原系数保持 | 两个原 pair 上指定 h248、admission 和 ordinary counts 的共同有向实现。 |
| U7,U8,U9 | 原两个槽、带标签源，U9 的多重出现保留 | 全 positive product 费用、unit/切尾、同一物理前缀的固定 cutoff。 |
| U10,U11 | 原四槽与同一 E，源的四维联合正分片成立 | 共用四前缀上的 switched/eligible ordinary minimum，所选全 square 与 selected square、末 ceiling、候选替换、U11 后续限制及其逐项付款。 |

T17 已从原 U3/U4 收据与各层的真实发出普通后裔得精确交集；原 full child=继承部分+rejectedChild，同一 Q 的 fixed query 还有非负 cutoff shell。这比“逆向桥完全缺失”强，但不表示每个原收据在所有获胜节点完整覆盖。T19 进一步给 owned fibre 上的 bank receipt budget，普通 W1 的整数端点与 W2 的旧前缀恢复/相同词 collision 在其冻结范围已处理；真正的 rejected-pair、positive switched 费用减 base reserve、收据壳、若干旧前代的有向差不能据此置零。T23 则掌管几何 full Member 与原 Θ；其书面 tuple 唯一性只计反馈树位置，不计所有 receiver/token 的累计重数。此包没有重新证明 T07 的经典分布/seed AP，没有借 H247 替 430，也未触碰 P1 final87。

并行续份进一步缩小这个开口：T17.successor 给同 E 的 106 行收据母式、负单窗及严格平方；T19.net-successor 的 owned_106_net 保留四个良好正 pair 的 E，直接收据行中已去掉正双子拒收壳，并将门外双子和长词留在实物费用。其 signed_price_identity 明写固定 outside、负单子 reject、正双子 reject 的各自符号；它没有证明这些壳与 switched/base 的净费用已非正。原 coherent Buchstab 的未加新 mask 的物理 profile trim 另已有 actual_buchstab_physical_trim_eq_zero，此处不再次列作欠账。T21 新东西是 **child mask 下**的严格 Buchstab 行。

## 缺口分级

- **形式化交付 / 未验证。** 八个 Lean 源提供上述明确的对象、恒等式与定量接口；未运行 Lean、Lake、LSP、stage、proofguard、producer、数值证书或 CI。无 kernel/transitive-axiom 结论。多快照的历史导入不能当作本地环境已经安装。另有上游历史依赖 P2EnhancedW1OrderedPositiveTripleWord 的冻结归档，T22 核得 SHA 2acb72eea087664d8dbc8bb5d24f69e489327b9a12acefb3b4c1a148313e6547；本包不进行 staging。
- **可以补足的原稿省略。** 同源平滑网格公分、所有实际祖先边缘、保留 fixed/equality/knot、原稳定图上的 proper 墙与总 Θ 控制、严格 Buchstab 新槽（两极性、immutable 旧系数、零 Θ 绝对付款）。对真父权、11 各行和各 signed base/floor/correction，细分本身不改变总数。它不能把带符号的 (Θ−1)·read 消为零。
- **决定全部 hLower 的实质开放接口。** 在同一原收据/母计数、Q、α、mark、owner 和 E 上支付 W1/W2 新的测试与普通/换结 base、adopted seed 和 rejected 账；把另外九项后续所需的政策、裁切与原实际 receiver 计数放到这张图上，证明相应混合误差与绝对/reserve。没有证明这些成本可从现有原行估计对任意过滤/子标签推出，也没有以共同 N₀、任意新 carrier、任意正 Q 或 hcells/hlocal 作输入。既有 P5OriginalFixedDensitySupplierAssembly.eventual_mean_of_fixed_original_grouped_suppliers 的 h34 仍未供应。未据此否定原稿结论，而是将仍需独立论证的接口定位到具体项。

冻结后交 T22 独立出具 REVIEW/ALLOWLIST；REGISTRY 的 SHA 用原始字节。所有写入仅在 T21 当前目录，不改 Git 树、原稿、main、其他作者代码。
