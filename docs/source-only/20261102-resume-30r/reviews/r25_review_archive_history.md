# R25：R03–R08 原档案、实际历史与两笔第五债务独立复核

**最终冻结审稿：R03–R08 窄源码范围通过；kernel 未验，零 formal credit。以下最终 raw pins 界定本次结论。**

本审计先读 R/BRIEF、DISPATCH 与 Q03 的 D01–D06，再独立阅读原稿、原第五 Jensen/Taylor 程序、Q 的相关包络／source／buffered-policy 文件、所需旧源码和本轮实际 proof bodies。结论只允许下表中的窄范围记蓝；所有本轮 Lean 仍 `compiled=false`、`kernel_verified=false`、`formal_credit=0`。没有新增绿色验收，没有执行 Lean、Lake、compiler、CI、数学 guard 或数值重放；闭有限 bodies 全部 UNEVALUATED。本人仅写本 review，不改作者源码、旧档案、生产模块、原稿、main.md 或 Git，不派子代理。

| 任务 | 可记蓝的实际源码范围 | 必须保持开放的原目标 |
|---|---|---|
| R03 / D01 | 47 个新桥接源域加 40 个已有源域的全87原行字典；ideal third 的上下界／四历史；full 与 selected squares；同 N 的实际 prime-frontier 转换 | 全部真实第六父策略、dynamic current-parent 上界、全87共同历史／分支成员及最终 rho 的来源 |
| R04 / D02 | 原 parent Jensen scalar floor／rounding；Taylor 原 log14、profile／ratio／weight 导数、原 affine branch 转换和 signed actual-owner 桥 | 原父几何与积分、实际 Taylor smooth-row 实例、完整带权 Hessian／五维 midpoint、stored-old 来源绑定与固定 oldBranchDefect 支付 |
| R05 / D03 | 全292633原父索引的实际 complete64 reserve ≤ 既有 gatePaidEnvelope；同一 e/q 达到任意 η、原 u_d/8 与 safe-fifth margin | 独立 oldBranchDefect；未扣旧债的原保存端点到完整实际第五积分；最终总密度账 |
| R06 / D04 | 具体原第四 bank 的共同 schedule；full-q 第四／第五／十四 source；positive-w 十四族包络；原十三族在十四族之后的两类 List 与完整 signed continuation 保持 | 十三族实际算术下界、其余原22增量在同一最终策略上的识别、full87／All22／hdensity |
| R07 / D05 | 全部实际 coarse／omitted 绝对加权和（含 disabled-small-third）；未 trim 历史 pair 边界；同 d、同 cutoff 的完整 ordinary catalog5 逼近 | 同一 full87 的 chronology／All22 接入、beta-attached 全策略密度与总 reserve；T=1 结果不能当任意 terminal 的误差估计 |
| R08 / D06 | Q22 buffering 后原第四／第五 signed gains 精确保留；既有 held compiledRho 的统一 rank/J0 和合并 beta/box 支撑膨胀 | 两对象的同一实现、完整全87高层 finite caps／历史、固定 C_policy、所有 gains 传输及两笔总 reserve |

上述“开放”不是据原稿之外的强目标退回本轮成果。本轮没有要求 full Python interpreter equivalence、完整 facet/polytope 穷尽，或所有不同上／下界 construction 共用一个人为 history 类型。正 saving 只需所用合法正子域；实际不利成本则必须按原策略完整支付。

**原稿依据与分类。** 原主稿 `../chen-imbalanced-semiprimes/paper/source/manuscript-body.tex` 的 SHA256 为 `ee6aecc164cc59f2d1fed1ad9e48f18f98472ab1d77ab425d53d93bc41ce56bd`。367–375 要求真实祖先、连续替换与原87域；435–449 要求 current parent≤R6、原 residual 和 full/selected squares；453–482 要求 own-prefix 冻结、equality/inherit 保留、先有限化再 N、支撑总膨胀小于1/1000；484–509 分开 density 与 compiler reserves；1327–1337 要求同策略四正项减22项、tail 单次替换。原 completion note 183–242 区分 physical cap 与 analytic cover、保留原 coarse decisions／small-third、禁止把子墙投影删除到父历史，并规定固定 C_policy 和参数次序。以上是真实必要义务。

本审计把 Lean API、import staging、有限 tactic 的可执行性归为(1)；已写的原行转换、导数／Jensen标量、加权墙面付款、signed continuation 与共同参数推导归为(2)。尚缺实际全局构造或完整积分供应不能仅称安装问题，但现有证据也不足把它升级为(3)原稿数学反例。没有发现可据以宣称原稿存在实质矛盾的证据。

**R03：actual source 与 actual current parent 分开。**

已读七份交付 Lean 的新语义正文，并对两份旧 literal 的精确来源另作字节核对。`P4AOriginalSeed7Unequal15Literal` 与 `P4AOriginalFirstFailureH5H7Literal` 的 import 至最终 namespace 段，和被冻结原 `.txt` 段逐字节相同，含原 CRLF；这两份是复用。第三份 ascending-fourteen literal 也是原表的转写：从原 release ZIP 读取行字符串，独立按 literalIndex→literalPool 重建十四族行序列，与原十四个域（原 IDs 0..14 去掉7）全部匹配；没有计算任一行的真假、几何点、积分或数值 guard。

`P4AOriginalRemainingEighthSources` 的 Source 仍量化全部原 strict affine rows，未将 PhysicalRows 当供应字段。common/branch row 的符号等式给真实门限、8个 full squares、各 unselected complement squares、selected licence 和所有旧 first-six 非空 tent 的上界；遗漏的 winning plane 由其原恒等式处理。`v=min(A,C)` 对任一所选平面给上界，未假定该平面在域外就是 active branch。selected 位置的辅助行只重用已有 largest-coordinate 条件，没有在 selected slot 假造 complement obligation。原 descending winner50 的部分行名写 selected184，但原 mask 与系数给134；新源用原系数证明134表达式，没有按行名改 mask。

最终 `P4AOriginalFull87SourceDictionary` 的 index 是真实族的构造子：47新桥接、descending15、ascending-pair13、H3十二域；globalIndex 的87双射只是标签算术。新增 all87 old-tent／W 上界确实由另外40域的既有 StrictRows 分支推出，随后使用原 gated、Theta-clipped ideal-third 六分支公式，保留其 Ordered／largest 条件。由此得全部87域的 ideal third≤comparison 及四个 odd histories；不是把 ungated v 扩大成域外 licence。

`P4AOriginalFull87PrefixBinding` 使 ideal third 真正读 reversed rank3 ancestor；实际 frontier 的坐标恒等式供给同 N 的 prime-product squares，保留 original carrier 和 target deletion。它仍有“该真实八前缀属于指定原 source”的结构前提，并不证明所有最终非零项均属于87个新动作。H5/H7 的 priority 消去来自原行36/37/(38)/18；其实际 guard 等价式仍明确保留 `H7<lambda6(ancestor6)` 与 `lambda6(ancestor6)≤R6`。这是正确的范围限制。

因此全87 **来源行／ideal-prefix 字典**可蓝；不能由87标签双射推出全部分支 disjointness／parent realization，更不能由 ideal third≤R6 推出后来已提高的 actual sixth≤R6。短词、inherit、equality 和最终全部后代的 actual membership／support 仍需完整策略供应。不能将本轮相应 source 字典再次列为“75域原行尚缺”。

**R04：真正旧分支的数学供应尚未到达 stored floor。**

原 subdivision 每父使用 `max(Jensen,Taylor,complete64)`，而 Q 包络的 `oldBranchDefectQ` 是保存旧值高于 complete64 的固定差额。原 `certify_fifth_prefix_jensen.py:70–74` 将 grid/lo/hi 各乘32，调用 adaptive 的 exact_term；parent 的 upper-log tail 是1/3，不能换成 child 的1/9后声称认证了原值。新 DirectedLog／RawFields 保留了原 tail、32-fold rescaling、完整整数 numerator/denominator、old log 的负号与 Q80 向下 rounding。143个未执行的 block bodies 聚合的是实际原行的标量条件；`all_original_Jensen_rounding_loss≤292633/2^80` 是 rounding 量，并非 oldBranchDefect。

Taylor 原程序16–19、26–55、59–94 的十四项 atanh 尾为 `2z^29/(29(1-z²))`。新 log14 和 midpoint lower 保留了 new-lower／old-upper 的相反符号与完整 weight。profile 文件用实际 firstF／firstSlope／firstCurvature 给原 m1、m2、mean-value 和 `min(m1(Dn+Do),m1*T+m2*delta*Do)` 相消界；不能仅用两个独立绝对导数和冒充此较强界。SignedKernel 文件保持 `4/(prod t*t5)` 以及两个各自 strict own-cube gates，在原[2,4] range 下接到 literal signed kernel，再用原 old15 majorant 的单向不等式接真正 licensed owner；没有把 old majorant 与 dynamic actual ancestor 强行设相等。

`P5OriginalTaylorAffineBranchBinding` 复用生产 Affine5 的 exact signed lower extrema。activeSide 采用原顺序：ascending 的闭上端点先测，再测 descending 的闭下端点。旧选择必须是 W 或真正 nonempty old mask，且胜过 W 与每个旧 active plane 的**有符号差**下界非负；由有限 max 的双向比较推出 rawFourth 等式。BranchFacts 没有积分或 cap-equality 结论作为字段，故此转换不是目标改名；但实际 archive 的 BranchFacts 仍未被实例化。

`P5OriginalTaylorAffineRatioDerivatives` 从 Function.update 下的真实 affine residual `(level−sum t)/t5` 推导一二阶坐标导数。末坐标保留 moving denominator，分别是 `(c5−s)/t5`、`−2s'/t5`；前四槽的二阶导为零。原 D/E/T 上界由实际 rawClosedBox、正 lower5、原 argument range 和新旧 argument gap 导出；tent/W 的 residualCoefficient 符号从原 affine expressions 证明。它没有将一个假设的导数界改名当作导数供应。

最终第九源 `P5OriginalTaylorWeightDerivatives` 同样识别真实 weight 在 Function.update 下的曲线，再证明导数。第5槽确有双重 reciprocal 因子，故轴幂为2，另外四槽为1；`w_i=−p_i*w/t_i`、`w_ii=p_i(p_i+1)w/t_i²` 和原 wmax/k/q 界保留这一差异。正 raw lower box 直接供给倒数乘积比较；这不是只证明漏掉额外 t5 分母的权重。九源仍未组合成完整 G 的二阶 bound 或五维积分。

D02仍缺：stored vertexGapSum 与真实父32顶点的等式和 whole-parent ratio licences→Jensen integral；实际 Taylor smooth/range/branch instances、完整 weighted Hessian 与五维1/24 midpoint；stored old 与原 Jensen／available Taylor max 的来源绑定。已知 stored-new=max(stored-old,complete64) 不等于该最后绑定。未得到 `sum oldBranchDefectQ=0`、任意小，或原未扣债 floor≤actual archive integral。不能用 R05 的 e→0 消去这笔固定旧债；也不能把本轮143标量 finite bodies 的静态存在当作 kernel 已验的旧积分证书。

**R05：实际 indexed reserve64 的必要转换已写出。**

这里复核的关键不是再次获得 history=empty，而是 `P5HistoricalActualReserve64Budget.lean:58` 的严格等式：同一 licensed owners 下，rawRetained 恰是 `indexedDomain ... e`，不是 zero-buffer domain。`:70` 复用真实 complete64 分割后，reserve 是一次 `M*volume(rawOmitted)+modulus(e)*volume(indexedDomain_e)`，没有额外乘64。

`:85` 将 e-buffer 的 rawOmitted 包含于 zero-buffer indexedOmitted 与**同批 owners**的0/e symmetric difference。`:102` 实际调用 selected/firstStop crossing 的 section/Fubini 结果得到 `428/75*e/400^4`，再以真实父盒体积 `1/400^5` 控制保留域。zero omission 经原 gate margin 与 Q 的 actual history 消去 gate/history 两部分，仅余 canonical filter。`:180` 中 `64*M*e` 是既有 strip rate 的上界系数，不是重复收取64个 child。`:211` 在全 ArchiveIndex 上一次求和进入原 gatePaidEnvelope；没有传入总 reserve 小量作为假设。

Schedule 的三个 theorem 用同一正有理 e 与同一 aligned q：先对任意η选 e，再以 `min(e/10,omega)` 选 q，保证 step≤e/20、≤omega/2。实际 child reserve 与 old-literal approximation 分别<η；源码和本审计均不声称二者合计<η。最后一条使用 `min(u_d/8,3037921066812732539869/302231454903657293676544−10051/10^6)`，因而是同一 schedule 同时保留两项严格余量，不是两个独立存在量词的拼接。余量正性的闭 norm_num 体仍 UNEVALUATED。

这已经供应 D03 的实际全父 child-reserve 小量叶子；既有 Q3/Q4、B13 或 empty-history 不再被用作它的替身。该 reserve 可以按更小η进入共同密度分配，不能借用 compiler u_c。这个结果不认证原 exact endpoint 总和，也不收回 oldBranchDefect；若完整第五端点需要同时用两类 approximation，必须按其实际误差各计一次，不能把“分别<η”当作共同一次η。

**R06：局部 source／positive-w 及十三族 current 保持成立的对象很明确。**

两个文件均固定原 `originalRows4/originalAdmission4`，由真实 admission predicate 的 soundness 推出 FourthGeometry，消去 caller 的 arbitrary bank／Geometry。原3,699,127是 wire List 长度，未被误用为 Finset 无重 cardinality；原 admission-filter bank 的实例化也不证明每条原 wire row 全部通过，或自动取得原 gain1 保存端点。

第一文件在同一个 policy6 上作 literal14 rank-eight splice，实际 physical source 的 new−current 恒等式保留 `roughPrimeUniverse`、List occurrences、incoming sign/mass、remaining primes、sign-sensitive beta 与完整 modulus test G。其正预筛终端使用原 `z=N^(19/96)`，先固定 beta，再令 e/omega/q/N 顺次选择；Q ordinary14 端点花η/2，actual projection 在**整个同一新十四树**上花另η/2，再用 raw current−new charge 恒等式代入。因此没有对两个 signed 树各取上界后错误相减，也没有把 signed difference 当单树 projection 的输入。这一次 beta 误差若进入最终 ledger 必须去重。

第二文件利用原十三 StrictRows 的 `t1+t2<mu`（零基坐标1、2）与 literal14 的相反 old-descending 半空间，证明十四族 guard 在原十三域必假。随后每个后代保留同一个 rank8 ancestor，所以不是只在根点 cap 相等，而是整段 signed recursion 与 actual policy6 相等。depth8 frontier List 先精确保留，再保留原 K/G reciprocal-weight selected list。另定义的物理 List 用 unit prime weights，并从实际 frontier 取得 primality/target deletion，证明其同一原 half-open primeBox 字典；full-q continuation 用 attachedLeafTest，未混入 K 的 reciprocal incoming mass。

这些是具体必要转换，不是全22 source association 结构字段。`ALL22_SOURCE_MAP.json` 仅是原 id/source/field/value 的 provenance 目录，不是22个实际增量的 Lean 供应。原13/28918解析 selectedSaving endpoint 已有；当前缺其实际算术下界与最终策略连接，不能再要求造一份相同 moment endpoint。第21/22项只是在原 winner9 seed 上逐次加强已采用估计的增量，不能再减一次完整 gain；四个 nonsingleton、旧 fifth replacement、third-tail 和原 chronology 的一次规则仍保留。

局部十四树、其十三域上的第六 continuation、held policy8 与最后 full87 并非已证明相同。其余动作若修改这些 continuations，仍须在最终共同策略上证明保留。因此 R06 不关闭 All22 或 hdensity。

**R07：最后三份源码实际支付了此前保留的 small-third source。**

四份源码针对 Q 的同一 before-third candidate List：它包含 old-rejected/new-admitted 候选，不能预设全部通过旧 cube。coarse 规范化字典保留 old／endpoint 的各自 own-cube gate，继而把 Q 的逐行统一误差乘回实际 `prod 1/(p_i−1)` 质量。List→tuple 求和采用已有真实 permutation/nodup 字典，不任意删除重数。固定正 h 后 active 第三素数≥N^omega、h≤omega，故完整 active mass 被实际正 prime box 质量控制；M+1 分配给出真正全 coarse absolute sum<ε。

历史 pair 的未 trim 差项使用实际 upper residual 的统一绝对界，包含 s=1；原域使两坐标均处于固定正下界3/16之上。M 的四条 proper walls 将完整 complement 包含于闭 strips，故 prime atoms／等号未被“测度零”免费删掉。实际 wall-prime mass、Q 的原历史 compact carrier 恒等式、M/J 的原 compact prime limit 与 integral trim limit，共同支付 untrimmed endpoint。没有由正积分推出有限 residual difference 逐点非负。

compact omitted 的 localization 也保留原 firstStop；它由同一 before-third 历史供给，而非另加外部假设。在 omega≤h≤t3 时，disabled-small-third 分支被真实 rough inequality 排除，只余两条 ordering walls；实际 gated lower residual 绝对界与闭 wall mass 支付它们。`smallOmittedSum` 则仍是 t3<h 的原 signed omittedRow，保持原 List、原归一化和原符号。

前四源的 GlobalLossReduction 精确保留 `actualSaving+smallOmittedSum−physicalSaving`，并没有把 unpaid tail 藏入ε前提。最后新增 SmallThirdMass、SmallThirdEndpointTail、SmallThirdPayment 三文件才真正消去它。此范围判断采用三份终端正文，而非仅根据作者“已付”摘要。

固定物理 gap 的来源尤其关键。原冻结 `P5OriginalAboveMuThirdLowerPhysicalCoefficient:42–43` 的 SecondRegion 恰为 `mu<x<rho`、`2v(x)−1<y<x`，其`:140–142` secondGuard 只读原 rank2 ancestor，和 d.e/chi/omega 无关。Q `P4ACatalogFiveActualPairDecomposition:405` 证明它等价于**整个**原 physicalDomain，没有新增 y≥3/16 过滤。J `P4AOriginalSecondPhysicalIntegral:60–82` 对整个闭 physicalDomain 给两端点分子 `v(x)−x−y`、`v(y)−x−y` 均≥rho。因此新 `guard_geometry` 没有 hGap 或另设有利子域前提；当 t3<rho/6，两 strict own-cube gates 和两 quotient≥N^(rho/2) 都从这些实际条件推出。此处 source API 的参数 rho 表示固定物理 gap，并未把 policy omega 改成 rho。

SmallThirdMass 在第一、二坐标的固定正区间[3/16,rho)使用既有 prime-box mass，第三坐标接真正有限 Chebyshev `sum log(p)/(p−1)`，得到第二矩≤M*h²，M先于h。它没有对零下端点虚用 Mertens 极限，原 prime atoms 与 target exclusions 保留。EndpointTail 的 tiny 部分消费真实 lower pair 的 Euler baseline 抵消后的绝对指数界及合法 moving budgets；middle 部分消费**完整实际归一化差**的 quadratic bound，不只取一个渐近误差项。所有 constants/阈值都先于后来元组。

wholeList 覆盖亦已供应。原 Q omittedRow:145–148 仅在 secondGuard 且未选 third 时非零；新 Payment:64 对原全部 candidates 按 guard／selected／small coordinate 逐项分解，guard 外按原定义为0，guard 内所有需要收费者由真实 primality、target deletion 和上述 gap 嵌入 tailBox。实际 incoming mass 被识别为原 reciprocal product，再用已有 occurrence→tuple sum 字典，不另加旧 admission 或 hGap。先得到 `smallOmittedAbsoluteSum≤tailAbsolute`，并非仅得到可疑的 signed cancellation。粗 harmonic H³由H≥1控制到既有 H⁵归一化 moving majorant，其 tiny 总量趋零；middle 的 Mh²给一个独立于h和全部 OriginalData 的D，最终 `smallOmittedAbsoluteSum<D*h`。

`exists_complete_omittedRow_payment` 将 small 和 compact 两部分的绝对和相加。`exists_complete_actual_catalog5_approx` 则先选 `h0=min(rho/12,epsilon/(4D))`，对每个0<h≤h0取共同delta,N0，再对所有满足原宽度且 omega=h 的同一 d 供应

`|normalizedActualSaving d N − physicalSaving| < epsilon`。

coarse 的 h≤omega 与 compact omission 的 omega≤h 因显式 omega=h 同时成立。其余 d 前提仅是原正 buffer、chi与mesh宽度，均列在结论中；tiny gap 不再对 d 另加限制。先 cutoff、后 widths／schedule、最后 N 的顺序保持，因此 D05 的原 ordinary 全域解析付款可按此窄范围记蓝，不能继续列 smallOmittedSum 为尚未供应。该 theorem 仍以 T=1、原 rough cutoff 及当前 secondChange 为对象；与 full87 后续 chronology、beta-attached 最终 density 和 All22 的同一系数接入仍是其他实际义务。

**R08：中间策略的 gain 传输与 held compiler 支撑各自可用，不能交叉当同一对象。**

`P4AOriginalBufferedArchiveContinuation` 的 originalSchedule 是原第四 admission bank 与原第五 archive。Q22 两个新 guard 严格在 first coordinate>mu，原有效4/5动作严格在 mu 下；等号落在原继承侧。非空前缀第一坐标沿后代不变，所以 depth2 frontier 上整段 signed recursion 能按地区分解；上侧两个旧策略都等于 old3，下侧新的 bufferedThird 等于 old3。由此原第四／第五 signed gains 对任意 terminal、weight 和 List carrier 精确保留。其 true-decision containment 另证，未用作 signed 单调性的替代。

这没有把原4/5 pointwise cap 变成 finite scalar cap table，更没有添加完整6/8动作或证明与 O 的 compiledRho 等式。它是一个明确的中间 continuation。

`P4AHeldTaggedCompilerSupport` 则一直针对既有 O/P 的同一 compiledRho。复用 E 已有 actual raw support<N^(299/500)，先于 fine mesh 和 N 固定 `J0=ceil((599/1000)/omega)+3`；从真实 rough prime lower bound、squarefree product 得 rank。outer/crossing 点通过真实 retained witness 与同格 label 长度得到相同 rank。同格 prime-label 的逐坐标比较沿原 canonical prime subword 相乘，控制收费点自身 `d≤N^(tau*rank(d))*e`，而不只控制 witness。

actual compiled rough 非零、原 small/rough 唯一分解与 sign-sensitive beta 的支撑 a<L，给同一总条件 `ell+tau*J0<1/1000` 下 compiledRho 非零处 q<N^(599/1000)。beta 与 box 没有各花一个完整1/1000；原 carrier 中零系数行也没有被误宣称满足支撑界。tau0 在 data/N 前选择；其结果是 support，不是 changed/mixed mass 付款或 PP。

因此两条窄供应可分别消费，但必须保留其对象边界。完整 full87、统一高层 finite caps/actual parent、固定 C_policy、实际全 changed/mixed 覆盖、同 rho 的 density 与独立 compiler reserve 均未由此获得。原 u_d/4 已用额度不变；本轮支撑膨胀不能被记作支付 u_d 或 u_c。

R08 REPORT:17 的“III 类尚未供应的全局构造”仍有分类术语歧义；本审计不据此认定第(3)类原稿实质缺口。该报告同时明确没有数学反例，实际所欠为本表列明的全局输入，须按此对象边界理解。这是范围分类澄清，不阻断两份局部 proof bodies 的源码结论。

**主清单与后续验收。** 已复核 root 的 R03–R08 README 范围表与 `E:/timot/Documents/FilesForGPT/Myath/output/r-batch-20261102/MAIN_AFTER.md` 的相关变更。最终计划 raw SHA256 为 `eda2afd45edaa3d00072bb677dd5eb3c9937c40d63ac23149ebbe3581cbeaca9`。其中第125行现明确原 T=1 ordinary catalog5 的 coarse、untrimmed、order 和 small-third 全域付款及 physicalSaving 逼近，与最终七源相符；第127行保留 R08 两对象边界；第26行将旧“75域”黄色描述修为 full87 actual parent／共同历史／原策略成员，避免重复已齐的源行字典。第128行 R10 同见证消费由 R26 独立复核，本审计仅确认其引用 R07 时不能重复计入旧 tail-bearing 版本。full87、旧第五 floor、All22、hdensity 等黄色边界保留，本轮零新增绿。

**最终字节与元数据记录。** 本次采用恢复后完整文件并重新核 pin，不将闪退留下的 Schedule／SignedKernel 空文件当作永久失败。最终交付 29 份 Lean 共 644402 字节，均非空且有 namespace 收尾；R03 的三份 literal materialization 明确计为原来源复用。最后修订的 R07 Mass 显式 import、Payment 的 `le_rfl` 与三角不等式 calc 已按最终字节复读。

独立逐 raw-byte 核对六份最终 REGISTRY 引用的 295 个文件 pin 记录（包含重复引用，非295个不同文件）、1447个声明行位置、5个原 ZIP entry pin，以及 R07 登记的120个直接 import 行位置，均零差异。下表的声明计数包括 new/reused/context 内带源名与行号的记录，重复项按记录计数；这里只核名称在记录行，不当作名称 elaboration。源码文本筛查未发现新 axiom、sorry/admit 命令、native_decide、#eval 或 #reduce；原注释中的自然语言不是 bypass。

| 范围 | Lean 文件 | 文件 pin 记录 | 声明行记录 | ZIP entry pin | 显式 import 行记录 | 差异 |
|---|---:|---:|---:|---:|---:|---:|
| R03 | 7 | 53 | 181 | 5 | 0 | 0 |
| R04 | 9 | 44 | 323 | 0 | 0 | 0 |
| R05 | 2 | 36 | 65 | 0 | 0 | 0 |
| R06 | 2 | 51 | 632 | 0 | 0 | 0 |
| R07 | 7 | 69 | 171 | 0 | 120 | 0 |
| R08 | 2 | 42 | 75 | 0 | 0 | 0 |

这些只标识本审计阅读的精确文件，不证明数学有限体已执行，也不认证递归 import closure 或 Mathlib API。以下 REPORT/REGISTRY 与作者最后通知的 pins 一致；根 README 当前 raw SHA256 为 `f906ff4c3c1a0c45548fb65a8ef517a1bc4efc06328bc33edbc575bdddcea3fa`，仅对其中 R03–R08 的范围表作本审计意见。

**R03 — `full87_source_history/`**

| 文件 | 字节 | raw SHA256 |
|---|---:|---|
| `P4AOriginalAscendingFourteenAffineSource.lean` | 11923 | `e5e7c88c94e3debd43ad523ecdcafcf3878852414f473037328761b0d73e5aaa` |
| `P4AOriginalFirstFailureH5H7Literal.lean` | 150476 | `c075ee740cadd6a6d2b4cd67fcd52825cad1a686da7db4380a527708dd57f852` |
| `P4AOriginalFull87PrefixBinding.lean` | 3649 | `0f3642ea1dceb4282c32d788970b06028b30267958a76f42026407ad96b8d394` |
| `P4AOriginalFull87SourceDictionary.lean` | 18650 | `dbfadaa879e08c2c3ecb270f699b84f3f9ac7b0b044ba96be8046da4a73c501c` |
| `P4AOriginalH5H7SourceDispatch.lean` | 5045 | `233f94b56da5c7b20153d818e71e4a334876b93a8aedeebc9f9d8a65727e5299` |
| `P4AOriginalRemainingEighthSources.lean` | 43893 | `cd0eeb7e27f7596c30da8576a065e94ae45d3aeb6c7e5dcde637709d9aced564` |
| `P4AOriginalSeed7Unequal15Literal.lean` | 138775 | `13cffcaf2b85775e9bd819401ae95b7b04708cb99ca7a6e11ba97bf721226b63` |
| `REPORT.md` | 10200 | `f3cd5abb8b24ecca6c4c3701a85a1b841c9a03a260261566ca0612d6717a3a22` |
| `REGISTRY.json` | 50714 | `d7c27c3eafc51a5451693bdee23aceb65475ffe9db1e2360bd317ca4dc1c10f3` |

**R04 — `fifth_old_defect/`**

| 文件 | 字节 | raw SHA256 |
|---|---:|---|
| `P5OriginalParentJensenArchiveScalars.lean` | 45756 | `765b815b86d09f08c76c0ef7a355b64e1603c96955d662254b5738903082b40b` |
| `P5OriginalParentJensenDirectedLog.lean` | 4610 | `0b8da7e27f9f3280cc98fc5d8526802bc2cdecfaa2ec5eeafa5ee92a8d98687b` |
| `P5OriginalParentJensenRawFields.lean` | 5957 | `5bffa30637eeecbed5c7a9fb5180bab46b579dc0fd50a1e9545eb2bda3dc7d9d` |
| `P5OriginalTaylorActualSignedKernel.lean` | 7949 | `8a8ac8100068d5c55a8e283dceb821dff0670a3bf722c0bbfb889839889fa518` |
| `P5OriginalTaylorAffineBranchBinding.lean` | 9740 | `cdc824d44c28ad72e0ac5c236a8d4845dbd4d6da2e12e5d356fc7d940beca8fd` |
| `P5OriginalTaylorAffineRatioDerivatives.lean` | 11436 | `d179af28c9f8032522d0ff3152c94233b8445dde06c5896c58bace5597b11ced` |
| `P5OriginalTaylorLogBounds.lean` | 5230 | `c91883e19db05ed0e290cb4133dc47e1f5215f49367a0d52b2e31b83446f7dc1` |
| `P5OriginalTaylorProfileDerivatives.lean` | 8104 | `c1fab4c9189b9c7a40f5d8901dad4131bf08669b422260bf79fc28040595481f` |
| `P5OriginalTaylorWeightDerivatives.lean` | 7597 | `a6d8934c29ee9114ce460d0c6a83711b8e372ed814ec05c6c6b1bcb53a06db42` |
| `REPORT.md` | 12765 | `3559cca8be4f78448209953d4109b0b3d7f14977460e0e2f9d15ea2e7378ae22` |
| `REGISTRY.json` | 74325 | `33a0139e25c11e958bea3f3947851956a62ba2c1e0898144b25918b6ce5c2600` |

**R05 — `fifth_reserve64/`**

| 文件 | 字节 | raw SHA256 |
|---|---:|---|
| `P5HistoricalActualReserve64Budget.lean` | 12729 | `327520490f00da4021a731c8b3f97536924febea466e4c4a50f1b7f7dcaad3da` |
| `P5HistoricalActualReserve64Schedule.lean` | 7202 | `44dbc670a70727072b737bc69e6ecaf3e8e9b95a41380bcb22de560849b82faf` |
| `REPORT.md` | 7747 | `c2ba72b4d7cc9c0a2eab1a577d9c654cb93de4f10cb090f7d90d82b29f0e5f6b` |
| `REGISTRY.json` | 36670 | `3298ee696d0c1fd3d3396c631fc4bc61c815fd2cd75aae7f3d7561cb5c03c5a9` |

**R06 — `all22_actual_sources/`**

| 文件 | 字节 | raw SHA256 |
|---|---:|---|
| `P4AOriginalArchiveFourteenPositivePresieve.lean` | 12256 | `ffa78a1c9331cc3d782d360d76aba438236672d42e98d43c36d7d30b437147e2` |
| `P4AOriginalFourteenThirteenCurrentSource.lean` | 13051 | `4e6514d3542c653f908b5222f923d31f940be1cf57d9da05c1fb34503a0f0945` |
| `REPORT.md` | 15163 | `75d9ff0c9e20f30007e4b69c03781de42188c14b11c5f41b150928b1b7d4d338` |
| `REGISTRY.json` | 118636 | `046e66051ff76e06645b6d5fd70a042f920e06eb4ad1e1442f7142350135ee68` |

**R07 — `catalog5_global_losses/`**

| 文件 | 字节 | raw SHA256 |
|---|---:|---|
| `P4ACatalogFiveCoarseWeightedPayment.lean` | 17891 | `d75c3fe5a6ad1b1cb0288a963c85883066cfb71c11b278d2170bd23385cbad40` |
| `P4ACatalogFiveGlobalLossReduction.lean` | 6503 | `d94fb146bdb77803d9b88fbafdb15a39a81ee332e639ea70ae29bc63371008aa` |
| `P4ACatalogFiveHistoricalPairBoundaryPayment.lean` | 13867 | `6f5e7afb57917f802a69f56e060d545eed88aa9c4b250d2a68405758b75eb066` |
| `P4ACatalogFiveOmittedOrderPayment.lean` | 18397 | `513c1f780a01b14daa00e389e76198b5c660db12cec0948eddb52f2ecf058259` |
| `P4ACatalogFiveSmallThirdEndpointTail.lean` | 10494 | `8b5b95d9c39fbe73105195416ebd898aa1ca75fb7001fc33c5c42f5de4f20e5c` |
| `P4ACatalogFiveSmallThirdMass.lean` | 7789 | `8ad9e0ac507338562765be5fe75cb6b91085336e93fd3dc9c1225c0a4d66b660` |
| `P4ACatalogFiveSmallThirdPayment.lean` | 15640 | `7df560c710c07b0c823f92c7bddc29f6ded9b8bf0f3246e5029aa186d8b5dfc7` |
| `REPORT.md` | 14060 | `b3913816c132b1806e6c40e4523e5f3607929c01ef6fc4ccbbeeef5f7458924f` |
| `REGISTRY.json` | 93726 | `1c088804cb23326f197e78db9c767f234ac6d9c8fdccd5d85180a6c57336b355` |

**R08 — `full_buffered_policy/`**

| 文件 | 字节 | raw SHA256 |
|---|---:|---|
| `P4AHeldTaggedCompilerSupport.lean` | 14514 | `3c7fdbdebd9c253aa9b5981437c38e91c3493afba83936037bfc49369408ca01` |
| `P4AOriginalBufferedArchiveContinuation.lean` | 15279 | `a6295e46d222916c2299ab8b58adcb3a79152ae914e595604d6cdecda6ea7aba` |
| `REPORT.md` | 11248 | `7f60e4006a6c8057bd88d347420821b4abe31c68e2936745d207826b2044d5b2` |
| `REGISTRY.json` | 34527 | `0ba876a248fa1d858cd7b3818cf21b532ef8dcbe7dff111be93e6751169166d3` |

**最终审查决定。** R03–R08 上表窄源码范围可接受为蓝；R05 的实际 indexed-reserve 小量与 R07 的原 ordinary catalog5 完整全域付款已供应，不再将这两窄目标或已齐的87原行字典重复列为待供。全87实际父与共同历史、固定 oldBranchDefect／未扣债第五 floor、完整 All22／原13实际算术端点、同 rho 的 density 与独立 compiler 总 reserve 继续开放。本轮对最终 hLower/hUpper/main-theorem 输入的删除为0；无新增绿色或 kernel credit。
