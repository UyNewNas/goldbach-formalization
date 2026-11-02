# R26 — compiler reserve / actual density reserve 独立复核

2026-11-02，审阅者 `/root/r26_review_reserves_density`。**作者冻结源码的窄范围静审通过；完整 All22/full87、总 compiler `<u_c`、剩余 density `<3*u_d/4` 与最终同 rho `hdensity` 均 HOLD。相关最终目标前提消除数为 0。**

只静态读取原稿、源码及登记元数据；只写本报告。未运行 Lean/Lake/compiler、CI、有限 guard、producer 或数值重放，未改作者、生产、旧批次、原稿、main.md 或 Git，未派子代。全文所谓窄范围 PASS 仅指源码与数学对象/前提边界的静态对应；`compiled=false`、`kernel_verified=false`、`formal_credit=0`，有限证明体均 `UNEVALUATED`，没有绿色节点建议。

仓库根为 `E:/timot/Documents/FilesForGPT/Myath/goldbach-proof-continuation`。R/Q/P/O 分别指 `docs/source-only/20261102-resume-30r/`、`...30q/`、`...30p/`、`...30o/`；Body 为相邻 `chen-imbalanced-semiprimes/paper/source/manuscript-body.tex`，Upper 为其 `modules/global-positive-upper-completion-20261010.txt`。先读 R/BRIEF、Q03/D07–D08、P t26 与 Q q30 最终审查；直接读 Body:453–509、Upper:183–242，并核实际关键 proof bodies。恢复后读到的是 `R/DISPATCH.json`，文件可解析；没有把并不存在的 `DISPATCH.md` 当成证据。复用检索包括 production、全部 source-only 和显式 ignored `.lake/proof-continuation/source-reviews/drafts`。

## 原稿义务与已有源码边界

| 原稿要求 | 直接核到的含义 |
|---|---|
| Body:453–461，Upper:206–224 | finite causal partition 在 N 前固定；祖先读取自己的 prefix；open inherit/equality 保留。even outer / odd inner 对同一完整 retained support 编译，再给正项 beta-plus、负项 beta-minus。 |
| Body:462–482 | 输出必须是同一整数 rho；physical cap、density 与 auxiliary analytic cover 不混换；support inflation 合计小于 `1/1000`。 |
| Body:484–509，Upper:211–242 | density `u_d` 与 compiler `u_c` 数值相同但为两个不同支出；先付实际误差才用 `E+u_d+u_c<K`。`C_policy` 固定在 fine atom count 之前，有限参数均先于最终 N。 |
| OriginalKLedger:139–187 | actual finite-third 已消费 `u_d/4`；全部其余 density errors 只剩 `3*u_d/4`。标量 split/精确 K 差额不支付任何新误差。 |

1. O `P4AUpperTaggedParityCompiler` 的 `changed` 为正号 `0→1` 或负号 `−1→0`；`coefficient_error_eq_changedMass` 和 `rough_density_increase_eq_changedMass` 是有限恒等式，尚无总质量小性。P `MixedWallPayment:55–81` 从被收费 d 本身取得同 tagged cell 的相反 canonical selection，`:132–173` 支付指定 proper canonical-prefix 墙族上的 strip × **完整** residual Euler mass；不含 fine atom 数因子。`:215–260` 以同一 beta slopes 给局部实际 rho 付款。这些具体源已存在，不能因未安装/未编译再说它们未写；其墙族仍不能无证充当全 mixed cover。

2. P `ContinuationAccounting:50–119` 的 exact physical increment 是 `Dplus*Mplus + Dminus*Mminus`。负 rough 改动 `−1→0` 的贡献是 **加 beta-minus density**；该 density 允许为负。`:123–140` 保留完整恒等式 `compiled = full raw + beta error + signed changed terms − actualPresieveCorrection`。单个完整政策的上界可利用 correction 非负舍去最后项；old-new saving 必须保留两个 correction 的差，不能相减两个无关上界。`:145–187` 实付 beta error，却明确留下两个 changed mass 未付。

3. O `P4ACommonPolicyTaggedCompiler:31–52` 的 tag 固定记录 old3/common3/policy4/policy5/policy6 的前九个 ancestor 决策，raw 是同一 `OriginalData` 的 held `policy8`；`:99–106` 是 old physical rho 的字面相等。held `policy8` 与实际原全87域的来源识别仍是独立义务。新 Q22 bufferedThird 候选也不能仅凭名字认成这个 raw rho。

4. `ActualCompilerDensityReserve:151–168` 已供应同 small weights、rough carrier 的实际 compiler slope，含不可遗漏的 `1/(nu*epsilon^2)`。`:196–214` 明确仍接受 raw bound 与 literal coefficient-error budget；重新包装该消费者不完成 D07/D08。`OriginalKLedger:104–137` 的 twoSupplierLedger 只替换 third tail 与 slot5 chart，四正项的 existing actual binding 也不使其余 quoted savings 自动变成同策略实际增量。

5. 不额外要求 full facet/polytope/Python interpreter 穷尽，不要求任意 signed sharp coupled-domain 的强化 PP，不把 held 模型的限制当原稿反例。完整负成本域、两个独立 reserve、same rho、全 mixed 覆盖及预先共同 schedule 都是原稿本身的必要要求。

## 本轮实际供应与验收边界

独立完整阅读 R06 两份、R07 七份、R08 两份、R09 三份、R10 五份新 Lean proof bodies；最终判断来自这些源码及其实际依赖，不以作者消息或 REPORT 的“actual”措辞代替证明体。以下 PASS 都仅适用于表中断言。

| 作者 | 本轮窄范围 `SOURCE_REVIEW_PASS` | 完整目标 |
|---|---|---|
| R06 / D04 | 原第四 bank 的具体参数消去；原 cutoff 的完整新 fourteen 正预筛包络；four/five/fourteen/thirteen 的真实 current-parent 与 full-q signed source 对应 | All22、原13 arithmetic endpoint、full87 仍 HOLD |
| R07 / D05 | 全 coarse 绝对加权误差、未 trim historical endpoint、compact order omission 与完整 small-third omitted absolute sum；同 d 的完整 ordinary catalog5 逼近 | 普通 catalog5 误差已供应；最终全87/full-q beta ledger 仍不由此完成 |
| R08 / D06 | 同 O held compiledRho 的实际 rank/support；Q22 后原第四/第五完整 signed gain 保持 | 两个具体对象不认同；全高秩 finite caps、full87、全 gain transport 仍 HOLD |
| R09 / D07 | 所有实际 changed 点的首个分歧前缀分类；有限共同 cap admission 子族的 proper-wall/full-residual 及同 rho beta 付款 | 全 changed 到子族的覆盖与总 `<u_c` 仍 HOLD |
| R10 / D08 | 实际 weighted own-cube cap 误差；Q22 同 mesh/buffer；消费 R07 全 ordinary catalog5 及 R08 原4/5 gains，在同见证下给完整 `catalogFiveCapError<eta` | 总 `<3*u_d/4`、最终同 rho `hdensity` 仍 HOLD |

### R06 — actual bank 的 positive-presieve fourteen 包络

已直接读 `all22_actual_sources/P4AOriginalArchiveFourteenPositivePresieve.lean` 的完整证明体和最终 cutoff 修订，并交叉读 Q `P2OriginalFourteenCommonScheduleEndpoint` 与 H `P5OriginalCommonPositivePresieve`。源码把 fourth bank 具体实例化为 `originalRows4/originalAdmission4`，几何由 admission test 给出；实际 fifth archive、current policy6、原 literal14 和 List occurrence 的 incoming sign/mass/remaining carrier 均保留。

`physical_fourteen_sub_current_eq_source:80` 保留任意 terminal G 的 full-q beta attachment，源符号为 new-minus-current；`raw_current_sub_fourteen_eq_original_charge:132` 的 saving 符号为 current-minus-new。`exists_original_bank_positive_fourteen_schedule:155` 是对**完整新 fourteen tree**做 positive presieve，再消费同一 ordinary charge 的 Q96 下界：ordinary 与 beta 各用 `eta/2`，没有对 signed difference 使用 projection，也没有同号单调性假设。最终版本使用原 `z=N^(19/96)`，以 `beta^2 <= (19/96)/nu` 保证 `w<=z`，由原 `mu=25/128` 导出 Q 端点所需的 `N^mu<=z`。其顺序是 `nu,eta,betaMax → beta,n,e0 → e,omega → q,N0 → N,cap`，全新策略的 beta supplier 对后选 retention policy 统一。

第二份 `P4AOriginalFourteenThirteenCurrentSource.lean:32–95` 用原十三族 `ascendingThird` 的 `t 1+t 2<mu` 与原十四族 `old_descending` 的 `mu<t 1+t 2` 排斥，导出十三族域上 fourteen 真正继承同一 `lambda6/policy6`；嵌套 ancestor 恒等式沿完整 later continuation 保持这个事实。`:98–144` 保存原 reciprocal-weight selected occurrence List 及其重数；`:147–229` 另建 unit-weight 的真实物理 frontier，prime-bank membership 的 primality/target deletion 来自实际 frontier，最后保留任意完整模数 terminal G 的 attached continuation。两类权重没有混用，旧 sixth 没有再减一次。

这只给具体 admission-filter bank、局部 fourteen tree 和上述 two-stage 原十三族来源；不证明全部 wire rows 的 analytic licence、不供应原13 arithmetic 下界，也不把任一对象认成全87/held policy8。其 beta 半预算属于该局部包络内部的实际支出，最后若再消费 R09/R10 attachment supplier，须按同一误差对象只记一次。R06 最终 REPORT 已明确此点。完整 All22 仍 HOLD。

### R07 — 实际 catalog5 的完整损失付款

`catalog5_global_losses/P4ACatalogFiveCoarseWeightedPayment.lean:171,264` 从真实 before-third frontier 取得 old/endpoint admission 的 strict own-cube gates，把实际 `coarseRow` 接到 Q 的 rawLevel residual supplier；没有假定候选已通过旧测试。固定 `0<h<=omega` 后，完整 active candidates 在同一 target-deleted `[h,19/96)^3` prime box 内。List 到 tuples 的已有精确对应保留原质量；最终支付的是**全部 occurrence 的绝对加权和**，不是单项误差或一个任意去重后的集合。

`P4ACatalogFiveHistoricalPairBoundaryPayment.lean:50,140,163,222` 用现成实际 upper residual 的 near-one 界覆盖 `s=1`，分别界住 pair 的两个 residual。完整 historical pair carrier 属于原 `[3/16,19/96)^2` box；原四条 trim proper walls 支付闭边界 strips，包含素数原子。trim 与 complement 精确拆分后接回 Q 的实际 compact carrier 和 M 的积分端点。没有从正积分推出 finite residual difference 逐点非负，也没有免费丢 firstStop/历史 pairs。

`P4ACatalogFiveOmittedOrderPayment.lean:145,235` 从实际候选历史导出 firstStop；在 `omega<=h<=t3` 上排除 disabled-small-third 分支，把真正未选点放入两个原 order strips。两个 gated endpoint residual 的绝对界与实际 `prod 1/(p_i-1)` 墙质量一起支付完整 compact omission。`:308` 的 `smallOmittedSum` 仍是原 List 上 `t3<h` 的**带原符号 omittedRow 和**，没有因为 action disabled 而设为零。

`P4ACatalogFiveGlobalLossReduction.lean:44,68,90` 的符号核对为

```text
normalizedActualSaving = normalizedHistoricalEndpoint
                         + normalizedCoarseSum - normalizedOmittedSum,
|normalizedActualSaving + smallOmittedSum - physicalSaving|
  <= endpointError + coarseAbsoluteSum + compactOmittedAbsoluteSum.
```

同一 `d.omega=h` 使 coarse 所需 `h<=omega` 与 compact omission 所需 `omega<=h` 同时成立。前四源将三项各分 `epsilon/3`，先给共同 min width / max N0，再允许所有满足原宽度条件的 d 与后来的 even N；它们保留的 `smallOmittedSum` 随后由以下三源实际支付。

`P4ACatalogFiveSmallThirdMass.lean` 取原 `[3/16,19/96)^2 × [0,h)` target-deleted prime box。前两坐标使用固定正 box 的现成质量极限；第三坐标使用已证明的 finite Chebyshev `sum log(p)/(p-1)`，连同全部素数原子取得 first moment `O(h)`、second moment `<=M*h^2`，M 先于 h。没有在零端点使用不适用的 Mertens 极限，没有将目标 source 换成不同 dyadic policy。

`P4ACatalogFiveSmallThirdEndpointTail.lean:42,58` 的 fixed gap 并非新输入：字面 `secondGuard` 经 Q 的 `secondRegion_iff_catalog_domain` 和 J 的 `physical_denominator_bounds` 给两项 numerator gap `>=rho=19/96`。`t3<rho/6` 因而导出**两个 strict own-cube gates** 和两实际 quotient levels `>=N^(rho/2)`。此处传给既有 generic API 的 rho 是固定 physical gap 参数；没有改变 policy 的 omega，也没有 h=omega 的循环论证。

`:109` 对同一个原 endpointDifference 分 tiny/middle：tiny 直接用 existing actual lower pair exponential bound，两个 residual 的**同 cutoff Euler baseline 已精确取消**，完整 tailEnvelope 的主 deficit 与误差都保留，再用实际 Euler product `<=1`；middle 直接调用 generic actual normalized difference `<=C/rho^3*t3^2`。阈值先于所有 h/tuple，包含 exceptional small terminal primes，没有只估显式渐近余项。

`P4ACatalogFiveSmallThirdPayment.lean:34,64` 从原候选 List 的实际 geometry、target deletion 和 omittedRow 自身的 guard 推出 tailBox membership。选中项的 omittedRow 为零；未选项保留完整 endpointRow。通过已有 Nodup/frontier-to-tuples 恒等式保留 occurrence 的 `prod 1/(p_i-1)` 质量，得到整个 `smallOmittedAbsoluteSum<=tailAbsolute`；不是假设 source 已在一个有利子域。

`:167` 将 tiny 项以 `H^3<=H^5` 接到现成 `normalizedMovingMajorant→0`，middle 项接到二阶矩，得到 `D>0` **先于 h 和全部 OriginalData**，随后每个固定小 h 有统一 N0，使全部 d 的 `smallOmittedAbsoluteSum<D*h`。`:231` 结合 compact order payment 支付**完整 omittedRow 绝对和**。`:262` 结合前四源给

```text
epsilon -> h0 -> any 0<h<=h0 -> delta,N0
        -> any OriginalData d with omega=h and the original width conditions
        -> every sufficiently large even N,
|normalizedActualSaving d N - physicalSaving| < epsilon.
```

没有 `hGap`、目标 tail 小性、目标 saving 或额外 cutoff 子域前提。h0 独立 e/chi/d，delta/N0 先于 d；原 e/chi/mesh 约束与此前相同。由此完整 **ordinary catalog5** 误差供应成立，前四源保留的小尾不再是这个普通比较的未付项。该 residual/source 的 terminal 仍为 `T=1`；最终全87、任意 beta full-q ledger 与其余总 density 成本仍需各自真实接线。

### R08 — 两个确切对象的供应，没有对象等同

`full_buffered_policy/P4AHeldTaggedCompilerSupport.lean:28,39,83` 直接复用 E 的真实 held raw support `<N^(299/500)` 和 rough prime 下界，构造 N 前的 `J0=ceil((599/1000)/omega)+3`，并把 retained witness 的 rank 转给实际 outer/crossing 的被收费 d。`:139,161` 从同 O floor labels 推出 `d<=N^(tau*rank)*e`，故 active compiled rough support 的膨胀是 `tau*J0`。`:200` 由同 O `rho_at_product` 的实际非零项取得正确 sign-selected small beta 因子 `<N^ell`，没有只给另一个模数的 support。

`:225,253` 使用的预算是**合计** `ell+tau*J0<1/1000`，不是分别小于同一个裕量。`exists_preN_held_compiled_support` 明确选

```text
tau0 = (1/1000 - ell) / (2*(J0+1)),
```

先于所有 `N>=2`、cap、合法 OriginalData 与 `0<tau<=tau0`。这确实消除了 held 对象的实际 J0/support-inflation 前提；它没有消除任何 mass-smallness 前提，也没有提供全87的高秩 cap 表。

`P4AOriginalBufferedArchiveContinuation.lean:34,51,66,69` 的另一对象是具体 `originalSchedule`：原 fourth byte bank/admission 和原 fifth owner；Q22 bufferedThird 用于 above-mu，原 fourth/fifth 用于 `<=mu`，等号保留原分支。非空 descendants 保持同一 first coordinate，原 first-two/firstStop 被保留。`:157–268` 由深度二 frontier 的 exact patch correction 推出 `original_archives_two_signed_gains`，对任意同一 weight、完整 terminal T、carrier 和 occurrence multiplicity 保持旧第四/第五**完整 signed gains**，无目标 gain 输入。

后一 buffered intermediate 不等于前一 O held compiledRho；原第四/第五保留公式也尚未成为全高秩 finite scalar cap tables。两份源码都没有声称全87、全 gains、固定全 `C_policy` 或两笔 reserve 已完成。这与最终 README 和主清单的“两对象分开”范围一致。

### R09 — 全点树分类、有限共同 cap 子族覆盖与该子族同 rho 付款

`compiler_reserve/P4AUpperTaggedFirstPrefixDisagreement.lean:56,98,137` 从已存在的 charged d/opposite canonical e 出发，在两条完整 valid selections 的最早不同 decision 处停止，前面的 decisions 全相等；同实际 tag 与 floor-label list 都保留。even 上筛 decision 恒真，所以该首个分歧确实是 odd prefix。它覆盖每一个实际 changed 点的**树递归分类**，不是遗漏负分支的正 retained 分类。

`P4AUpperTaggedFrozenAdmissionCatalogue.lean:31–165` 进一步把真实 canonical prime prefix、同 O label 和 sup-norm 距离 `<=tau` 接到既有 `ordinaryRosserPrefixAdmissible` 的原 total-product/全部 odd-cardinality cube 字典。**同一冻结 cap** 下的真假翻转在 d 本身定位至 proper affine row strip；两 tuple 的原 strict order 已证明。零行不能有真假翻转，由此排除 identically true/false row；没有把 equality/inherit 层当零测集删除。

`:168–273` 的 finite cap `levels`、`rowConstant=1+sum norm(row)` 与 proper rows 都在 fine atom 之前固定；`frozenAdmissionMixed` 明确定义为有同 cap opposite prefix admission 的实际子族。该子族到固定 catalogue 的覆盖被证明，随后 P 的 strip × **完整 residual** supplier 支付字面 `sum_d 1/phi(d)`。这里没有 atom-count 乘子，也没有把 `levels` 作为原全策略已经存在的 cap 表。

`P4AHeldTaggedFiniteAdmissionPayment.lean:30` 真正调用 R08 的同 held crossing rank 来界首个前缀；没有新 rank/support 假设。`:60–136` 将各有限 rank 子族并在实际模数上：一个模数在 union 中一次，多 rank/witness 只会让比较和更大；分配容差后取有限正 inf width、finite sup N0，uniform 于后来 keep/tag/cap 与更细 tau。`:151` 逐 occupied small/rough product 证明这个受限物理和的条目就是**同一全局 O rho**，包含真实 sign attachment。`:175,193` 用 O 的一单位 discrepancy 和已有实际 beta slope `B/(nu*epsilon^2)`，在 beta precision 已固定后选择 tau/N0，给该完整子族的任意小物理误差。

关键未供的箭头仍是

```text
all actual changed/mixed points
    -> admissionUnionModuli of an actual fixed full-policy catalogue.
```

即使仅对 held constructor，这个全覆盖也没有证明；owner/guard、两边不同 cap、variable maxima、short/inherit 以及全87分支的实际分类还不能由“首个分歧”自动推出。新 theorem 没把这个缺口偷换成 caller 的 coverage/error 字段，而是只证明明确子族。固定 row norm 与定性 wall limit 也没有证明原稿完整 `C_policy*tau*omega^(-5)` 率。故全 coefficient norm、完整 signed compiler difference 与总 `<u_c` 一律 HOLD。P 的 negative continuation 与 old-new presieve correction difference 保持原状；局部 absolute upper bound 没有改写其 exact sign ledger。

### R10 — 真正的实际 cap 付款与同见证部分 density 目录

`actual_density_reserve/P4AActualOwnCubeCapPayment.lean:28,40,73` 在既有 canonical lower factor 上证明 own-cube 边界的零延拓和 compact cap modulus。失败及等号成本为零是解析 profile 的已证事实，实际 arithmetic strict gate 仍在。**canonical modulus 统一所有 rank；算术 N0 是逐固定 rank**，不是一条 unbounded-rank uniform arithmetic theorem。`:134,181` 复用原 `P1VariableOwnCubeResidualUniformity` 的 all-cap supplier，在同一 target-deleted prime tuple 比较两 cap，再用实际 `actualPrimeBoxMass` 对 `prod 1/(p_i-1)` 绝对误差求和。delta/N0 先于任意后来 subset、mask 和两张 cap 表；无每格成本、factorial 或 arbitrary coefficient mass 前提。

`P4AActualBufferedFallbackCapPayment.lean:32–55,91` 选的是 Q22 真实 `selectedThird` 上的 secondGuard/thirdGuard tuple carriers；二者互斥。它消费同一个 m、正有理 buffer，分别比较有限 fallback cap 与原 `v(second)` / `v(second+third)`，两项各 `eta/2`。`:143` 可选局部 `<u_d/8>`，但没有据此声称全剩余账本只剩 `5*u_d/8`，也没有把该项自动认成最终 rho 的全改变量。

`P4AActualLocalDensityCatalogue.lean:35,49` 把 R07 全 coarseAbsoluteSum、完整 historical endpoint-to-physicalSaving 误差及 R10 两 cap defects 定义为一个实际局部目录，三部分各分 `eta/3`。它直接调用 R08 `original_archives_two_signed_gains`，不是新加 gain equality 假设：同 originalSchedule、同 m/buffer 和共同 N0，所有后来 N 同时满足局部成本与原4/5 signed gain 保持。

保留尾项的中间终端在 `P4AActualSmallTailDensityCatalogue.lean:67`。它消费 R07 的 actual-saving reduction（内部含 coarse/endpoint/compact omission），给这部分 `eta/2`；两 cap defects 合给另外 `eta/2`。`:44` 的三角不等式和结论为

```text
tailReducedDensityError < eta,
catalogFiveCapError <= tailReducedDensityError + abs(smallOmittedSum),
catalogFiveCapError < eta + abs(smallOmittedSum).
```

这里的 `smallOmittedSum` 是 R07 的同一实际 signed source，不是任意 residual 字段；该文件没有假设或断言它小。这个目录替代 `localDensityError`，二者的 coarse/endpoint 成本重叠，不能相加。

**最终最强终端**是新增 `P4AActualCompleteCatalogFiveCapPayment.lean:43`：直接消费 R07 `exists_complete_actual_catalog5_approx` 的完整 ordinary source 误差 `<eta/2`，再在同 d 消费 Q22 两 cap errors 合计 `<eta/2`，得原来定义的 **`catalogFiveCapError<eta`**。没有 `smallOmittedSum`、hGap、目标 density/误差作为前提。它的构造顺序为

```text
eta -> a0 -> any 0<a<=a0 -> delta
    -> original e,q,chi,omega with omega=a and the original width conditions
    -> one actual m,buffer -> N0=max Ng Nb -> all later even N.
```

同一 m/buffer 同时用于 R08 原4/5完整 signed gain 恒等式；各项都是同一 originalSchedule.data。枚举 cap 取实际 N，覆盖 `N^(19/96)` 的不等式已从原指数导出。该完整目录再次**替代**先前两份 partial catalogue，不能把它与已经包含的 coarse、endpoint、compact/tiny/middle 或两 cap payment 相加。完整 ordinary catalog5 与两 cap 的局部实际成本已付；其余 full-policy 成本、全87、与 O held compiledRho 及最终 beta rho 的 source dictionary 仍未供应。旧参数的原几何条件是实际可消费范围，源码没有宣称构造了兼容所有其他 upstream obligations 的最终全局 schedule。

以上五源没有 `All22Actual`、`hdensity`、总成本小性或目标 saving 作为新前提。它们供应的是明确实际 costs，而不是又一个“若总误差小则 density 小”的消费者；因此窄范围有新数学内容，同时完整 D08 仍 HOLD。

## 不能越过的最终接口

| 账项 | 独立核对后的可记范围 |
|---|---|
| 已有第三 finite-density | 已花 `u_d/4`；本轮不重花。其余实际 density errors 总共只能用 `3*u_d/4`。 |
| R06 positive14 | 普通源 `eta/2` 与完整新树 beta `eta/2` 已在该局部包络内合并；不是另外两笔免费裕量。尚无最终全账本 allocation。 |
| R07/R10 catalogue | R10 直接消费 R07 完整 ordinary catalog5 已付项；最终 Complete 目录已无 tail，替代 Local/SmallTail 两目录，不能重复相加。局部可选 `u_d/8` 或任意精度，不等于全 density 账 debit 已闭合。 |
| 第五 old defect / child reserve | R05 的 reserve64 实际小量/裕量付款与旧 floor 缺陷分开；本报告不把未付 old defect 改称可任意缩小的 mesh error。 |
| compiler | `u_c` 为独立第二笔 reserve。R09 子族物理误差可按任意小正精度付款，但尚未覆盖全 changed，不记总 `<u_c`。 |
| exact scalar slack | `E+u_d+u_c<K` 只在两笔实际总成本已支付后适用，既不能补 tail，也不能解决 same-rho/source mismatch。 |

| 完整目标 | 本次验收所需实参 |
|---|---|
| 全 mixed compiler | 每一 actual changed/mixed/tagged point 属于固定 proper-wall/tail catalogue 或精确 identity/inherit 层；完整 signed continuation、same beta、presieve correction；固定 policy 常数；总 `<u_c`。 |
| density 剩余预算 | 同一个实际 signed ledger、catalog5 全域误差、其余 finite cap/wall/tail/attachment 总成本 `<3*u_d/4`，已付项只记一次；第五 old defect 与 child reserve 按其真实证书债分别处理。 |
| shared parameter schedule | 同一 policy/beta/omega/J0/tau、真实支持上界与 N0；不能从各自独立的 existential choices 自动得同一 schedule，也不能在 N 后反选 refinement。 |
| hdensity | 上述实际供应消费到最终同一 `attachedUpperCoefficient/moduli`；不得把目标 density 或目标总 error 作为新 premise 后记完成。 |

已直接读 `ImbalancedChen/P4BCurrentSmoothBadUpperSuppliers.lean:40–52`：`hdensity` 与 `hUniformPP` 绑定同一 `attachedUpperCoefficient nu r (epsilon delta) (retain delta) (cap delta)` 及同一 `attachedUpperModuli`。本轮新结果中，R06 的 fourteenPolicy、R07 的 ordinary secondChange、R08 的 buffered intermediate、R08/R09 的 O held compiledRho、R10 的实际 partial cost 并未被证明是这个共同最终系数的完整 ledger。只在 R09 子族中已证明 occupied product 的 global O rho 等式。最终 same-rho `hdensity` 实际前提消除数仍为 **0**；R19 的另一个 roughPrimeReserve exact-zero 结果也不是这个 density 输入。

R25 交叉消息指出 R05 已有 actual reserve64 的局部任意 eta schedule，oldDefect 另留；此处未复审其全部解析 proof body，不替 R25 扩大验收。尤其两笔分别 `<eta` 的 literal error 与 child reserve 合起来不能报 `<eta`；若用原第五 endpoint 自身的正裕量吸收，需保留具体比较和一次支出，不可只称二者随 mesh 自动消失。

困难分类沿用 Q03:21：I 是表达/API/安装与未执行验核；II 是有确定数学对象的可补省略；III 是真实来源、全域估计尚未供应的深层义务。新 actual cap/source 转换、完整 ordinary catalog5 加权付款（包括真实 smallOmittedSum）与 R10 同见证推导属于已补 II。全87共同有限实现、完整 mixed cover/量化政策率、总 density 与同 rho 装配继续按 D06–D08 记 III。**III 不表示已找到原稿反例**；没有借模型范围限制、新增稿外要求或目标同义假设作此判定。

## 最终静态元数据与根范围文本

逐字节核对五份最终 REGISTRY 的全部 `path + sha256/raw_sha256` 引用；核对记录的 bytes、Lean line_count、声明位置及 direct-import 文本。下表的声明/import 数为登记引用次数，包含复用项，不是新 theorem 数，也不表示传递依赖闭包已经验证。

| registry 所属目录 | hash 引用 / 不同路径 | 声明位置 | import 文本项 | 结果 |
|---|---:|---:|---:|---|
| all22_actual_sources | 51 / 51 | 632 | 104 | 无差异 |
| catalog5_global_losses | 69 / 50 | 171 | 120 | 无差异 |
| full_buffered_policy | 42 / 35 | 75 | 7 | 无差异 |
| compiler_reserve | 38 / 33 | 91 | 55 | 无差异 |
| actual_density_reserve | 47 / 43 | 373 | 104 | 无差异 |

R09 消费的 R08 support pin 与 R08 冻结字节一致；R10 消费的 R07 七源和 R08 archive-continuation pins 与作者最终冻结字节一致。19 份新 Lean 非空、完整 proof body 已读；对这些新文件的文本检查未发现 `sorry/admit/axiom/unsafe/native_decide/implemented_by/#eval/run_tac/opaque` 项。此检查不替代 Lean elaboration、依赖 axioms 审计或 kernel 验证，未执行任何有限证明体。source-only import 路径可定位，不等于已部署或完整递归闭包已验收。

根 README 已抽核 R06–R10 scope 行，`MAIN_AFTER.md` 已核 R06 行52/62、R07–10 行123/125/127/128 及总目标行129/130/137；与本报告的窄范围/继续 HOLD 一致。仅针对这些行认可源码范围，未改根文件、原 main 或其他审查范围。读取的根文本快照为：

| 文件 | raw SHA256 |
|---|---|
| R/README.md | `f906ff4c3c1a0c45548fb65a8ef517a1bc4efc06328bc33edbc575bdddcea3fa` |
| `../output/r-batch-20261102/MAIN_AFTER.md` | `eda2afd45edaa3d00072bb677dd5eb3c9937c40d63ac23149ebbe3581cbeaca9` |

## 作者冻结 raw SHA256

下列路径均以 R 为前缀。哈希是本次独立读取原始 bytes 得到的结果；不据此执行原始 archive 的解析、guard、数值比较或任何数学证明。

| 文件 | 行数 | SHA256 |
|---|---:|---|
| all22_actual_sources/P4AOriginalArchiveFourteenPositivePresieve.lean | 217 | `ffa78a1c9331cc3d782d360d76aba438236672d42e98d43c36d7d30b437147e2` |
| all22_actual_sources/P4AOriginalFourteenThirteenCurrentSource.lean | 232 | `4e6514d3542c653f908b5222f923d31f940be1cf57d9da05c1fb34503a0f0945` |
| catalog5_global_losses/P4ACatalogFiveCoarseWeightedPayment.lean | 335 | `d75c3fe5a6ad1b1cb0288a963c85883066cfb71c11b278d2170bd23385cbad40` |
| catalog5_global_losses/P4ACatalogFiveHistoricalPairBoundaryPayment.lean | 265 | `6f5e7afb57917f802a69f56e060d545eed88aa9c4b250d2a68405758b75eb066` |
| catalog5_global_losses/P4ACatalogFiveOmittedOrderPayment.lean | 339 | `513c1f780a01b14daa00e389e76198b5c660db12cec0948eddb52f2ecf058259` |
| catalog5_global_losses/P4ACatalogFiveGlobalLossReduction.lean | 120 | `d94fb146bdb77803d9b88fbafdb15a39a81ee332e639ea70ae29bc63371008aa` |
| catalog5_global_losses/P4ACatalogFiveSmallThirdMass.lean | 167 | `8ad9e0ac507338562765be5fe75cb6b91085336e93fd3dc9c1225c0a4d66b660` |
| catalog5_global_losses/P4ACatalogFiveSmallThirdEndpointTail.lean | 190 | `8b5b95d9c39fbe73105195416ebd898aa1ca75fb7001fc33c5c42f5de4f20e5c` |
| catalog5_global_losses/P4ACatalogFiveSmallThirdPayment.lean | 301 | `7df560c710c07b0c823f92c7bddc29f6ded9b8bf0f3246e5029aa186d8b5dfc7` |
| full_buffered_policy/P4AHeldTaggedCompilerSupport.lean | 278 | `3c7fdbdebd9c253aa9b5981437c38e91c3493afba83936037bfc49369408ca01` |
| full_buffered_policy/P4AOriginalBufferedArchiveContinuation.lean | 271 | `a6295e46d222916c2299ab8b58adcb3a79152ae914e595604d6cdecda6ea7aba` |
| compiler_reserve/P4AUpperTaggedFirstPrefixDisagreement.lean | 181 | `21d7de9cdebe681296f66088b73c9abe870b5837053d9c30ac5f48488785834a` |
| compiler_reserve/P4AUpperTaggedFrozenAdmissionCatalogue.lean | 276 | `0f60783ed11d8a289a597da99c59b59391a12b57eef4d40df3a720c54d27e5cb` |
| compiler_reserve/P4AHeldTaggedFiniteAdmissionPayment.lean | 239 | `e34f4b1fadca00f8405d65cd487191c9716f9b2eb074bfaaba1a2e33d8c2b987` |
| actual_density_reserve/P4AActualOwnCubeCapPayment.lean | 231 | `54f42c9032005da8824d9964983a6dc6d4e48fe56279a25e768bb0a26bbed5ec` |
| actual_density_reserve/P4AActualBufferedFallbackCapPayment.lean | 157 | `d2e52e96d552bc379c11c40ba577608de113ab8d6e16ca54fba9e54b5c8e3967` |
| actual_density_reserve/P4AActualLocalDensityCatalogue.lean | 107 | `8074db3e905fb6d28b06698ac9b4563febb6dfe91c00607d27c6b6bd873d0d79` |
| actual_density_reserve/P4AActualSmallTailDensityCatalogue.lean | 125 | `113063fa7f696070c2099211f9dd2653ba6309ef8733c735b1e16ef1d6041c07` |
| actual_density_reserve/P4AActualCompleteCatalogFiveCapPayment.lean | 103 | `553c8e61df3e1d699955bdd671cd29b06ae4f01082c2c06eaee5d76e6e9b23ba` |

| 作者目录 | REPORT.md SHA256 | REGISTRY.json SHA256 |
|---|---|---|
| all22_actual_sources | `75d9ff0c9e20f30007e4b69c03781de42188c14b11c5f41b150928b1b7d4d338` | `046e66051ff76e06645b6d5fd70a042f920e06eb4ad1e1442f7142350135ee68` |
| catalog5_global_losses | `b3913816c132b1806e6c40e4523e5f3607929c01ef6fc4ccbbeeef5f7458924f` | `1c088804cb23326f197e78db9c767f234ac6d9c8fdccd5d85180a6c57336b355` |
| full_buffered_policy | `7f60e4006a6c8057bd88d347420821b4abe31c68e2936745d207826b2044d5b2` | `0ba876a248fa1d858cd7b3818cf21b532ef8dcbe7dff111be93e6751169166d3` |
| compiler_reserve | `9594dd7eb6fc8be246f7099dc592834912eff2bda39d72f229c9919788a34af9` | `634652f0e2faf3e4bb2501db25d0fdf9e68b9f1af6fa39784cd8ebaec2feab24` |
| actual_density_reserve | `6eff01a117c145edfed63fdff9cdacce5dba98d14b04a7c1332653423b59c6d0` | `34b0bab72dbba257b65718bc9f16a777c44c793bd79eb240e0b1eb39fa884a04` |

## 基线 raw SHA256

| 文件 | SHA256 |
|---|---|
| Body | `ee6aecc164cc59f2d1fed1ad9e48f18f98472ab1d77ab425d53d93bc41ce56bd` |
| Upper | `49d61d20569c83bc05e6221992262c9c42aea275b90ab67d74b0d33514832a42` |
| R/BRIEF.md | `3643ffc4134691ee32a782a2ff1afa9c351dd9fd5c1686f667fd7159b63baa67` |
| Q03/NEXT_DIRECT_PROOF_REVIEW.md | `5645cbf9204d7ed41cd458ce5a46c4b5f9ccd72817c37d437c82f8e032c18f78` |
| P/reviews/t26_review_policy_reserve.md | `e0c1a9bd0ab8fc8708bef66df1f158ee193d2de4181a3305566edcc06221229a` |
| Q/reviews/q30_review_history_final.md | `436780998c45664f07328cbf7dc4d6b7648144df8ac30c040b8c51e326b2cd2d` |
| ImbalancedChen/P4AAll22OriginalKLedger.lean | `c868f088df2402058fa4be33896e7894aa078a2f1d7f67de7dc8adc0df3404b5` |
| ImbalancedChen/ActualCompilerDensityReserve.lean | `c774a48050ce70a5aefc234ee898e173bb75a1b4fa03f7342e5ffb0b6b17deae` |
| P/actual_two_reserves/P4AUpperTaggedContinuationAccounting.lean | `66fccf58bbd090023c999ffe4f6ab49860f21aac569a943a682897b14c577337` |
| P/actual_two_reserves/P4AUpperTaggedMixedWallPayment.lean | `f35e43631e01a6ca56188d8f71a5c0d66806ede6e151e16a5dfa8818fd078cc6` |

本报告只接受上述冻结源码的限定结果。没有新增绿色或 formal-credit 节点建议；没有把未执行验核、未安装 imports、尚未完成的来源义务混为一类，也没有把两笔总 reserve 或 final density 记为完成。
