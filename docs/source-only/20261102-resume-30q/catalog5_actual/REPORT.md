# Q21 — actual catalog5 source conversion

日期：2026-11-02。仅交付本目录三份严格证明体候选及登记表；`compiled=false`、`kernel_verified=false`、`formal_credit=0`，finite guards 为 **UNEVALUATED**。完整 catalog5 历史源极限、`P1.4.history`、`P4A.4.actual_all22`、`P4A.5.hdensity` 均保持 **OPEN**。本批完成的是下面四个窄供应，不把其中任何一个称作两笔 reserve 或最终同一 rho 密度结论。

路径均相对 `E:/timot/Documents/FilesForGPT/Myath/goldbach-proof-continuation`。完整新声明、直接 imports、复用文件及原始 SHA256 见 `REGISTRY.json`。未安装这些 modules，未声称当前 import closure 可编译。

| 新源文件 | 已写出的实际供应 |
|---|---|
| `P4ACatalogFiveHistoricalCoverage.lean` | 真正 `HistoricalThirdCoarse.cells` 全闭有序矩形的覆盖；从 P 的 before-third candidate 推出已通过的同一 firstStop；未选第三点只落在 small-third 或两个 order strips；统一旧网格阈值先于 N。 |
| `P4ACatalogFiveActualPairDecomposition.lean` | 真实 retained/restored source 与同一 rank2 历史上的 endpoint pair source 的精确有限恒等式，保留两个显式差额；真实 upper residual、权重及 normalization 字典；有 clearance 的 K/M compact trim 上，实际历史 Finset 与 M Finset 精确相等。 |
| `P4ACatalogFiveCoarseResidualUniformity.lean` | 固定正 cutoff 上，单一 N0 统一全部 `lambda≤Theta` 的实际 strict-own-cube lower residual；真实选中 coarse `rawLevel` 到 `N^v(x)` 的任意小 gated summand 误差，并从旧选中 cell 供应 first cube。 |

先读 Q/BRIEF、P `all22_common_history/REPORT.md`、`REGISTRY.json` 与 `reviews/t26_review_policy_reserve.md`，再核原稿 `manuscript-body.tex:371–509,1327–1369` 和 `modules/global-positive-upper-completion-20261010.txt:55–281`。主稿 SHA256 为 `ee6aecc164cc59f2d1fed1ad9e48f18f98472ab1d77ab425d53d93bc41ce56bd`；source note 为 `49d61d20569c83bc05e6221992262c9c42aea275b90ab67d74b0d33514832a42`。

主稿 371–374 要求 successive new-minus-current-parent；379–418 要求实际有限树及 ordinary residual；453–482 要求先于 N 的共同 causal approximation、各自祖先标签和保留 identity/inherit 区域；494–509、1327–1337 要求四正项减全部 22 saving，完整第三 tail 只替换一次。source note 185–188 明确 physical caps 始终是 coarse `lambda_B`；198–216 单列 small-third bound、proper-wall trimming 及 h→buffers/widths→higher caps 的次序。这些要求没有被端点 pair 极限取代。

有限恒等式使用 P 的原 candidate List，而非旧 rank3 admitted frontier。令 `E` 为两个比较 endpoint trees 的根差，`C_s=coarseRow s`，`O_s=omittedRow s`。`second_saving_eq_endpoint_add_actual_discrepancies:213` 和 `retained_restored_saving_eq_endpoint_add_actual_discrepancies:233` 给出

`-secondChange = E + Σ C_s - Σ O_s = -Σ(retainedTerm + restoredTerm)`。

这里两棵比较树都保留 actual `old3` 的 rank1/2 决策；它们并未改写实际 secondStage、physical parent 或最终 rho。`C_s` 在实际 selected 且 secondGuard 成立时，严格定义为 actual old admitted continuation 减 old endpoint admitted continuation。`O_s` 在 secondGuard 成立而 third 未选中时，是完整 endpoint difference。所用 `admittedTest` 保留布尔接纳门；旧拒收/新接纳的恢复项仍是完整新 continuation，不能给它补造一个旧 residual。恒等式逐 occurrence 保留 sign、mass、remaining carrier 和任意 terminal test `T`，未假设 source equality 或误差小性。

`omittedRow_small_third:245` 对 `p3<N^omega` 明确给出 `O_s=endpointRow s`、`C_s=0`。实际动作在这支为零，并不意味着比较端点项为零。其完整影响在减去的 omission sum 中保留。

`endpointSource_eq_historical_pair_sum:264` 用已有 rank2 splice identity 取消共同 stopped 部分。`pairEndpointRow_eq_actual_upper_residual:353` 从真实 rank2 frontier 和原 secondGuard 推出两端点的 ordinary prefix admission，含 total-product 与 first-cube tests；随后才使用实际 **UPPER** residual。P 的 rank3 **LOWER** 与该 rank2 upper source 由有限树恒等式连接，不是两个独立筛界的相减。

`endpointSource_eq_historical_tuple_sum:433` 使用真实 `roughPrimeUniverse` 的 Nodup 与已有 List→Finset reindex。`normalized_endpointSource_eq_catalog_summands_on_actual_pairs:478` 把 summand 精确识别为 K/M 的 `actualPrimeTupleInitialSaving`：同一目标删除、同一 cap、strict last-prime cutoff、完整 product，以及 `∏ 1/(p_i-1)` 和 `log N/C_N`。`v_eq_catalog_endpoint:397`、`secondRegion_iff_catalog_domain:405` 保留原开域；没有 Chen quarter、排序 factorial 或额外 2。

compact carrier 已有实际证明，不能继续列为未供。`catalog_trimmed_pair_mem_historical:498` 在 `delta>0`、`e≥0`、`4e+meshStep(m)≤delta`、`N>1` 下，从 K/M trimmed pair 的本身数据推导 actual firstStop、initial first cube 及完整历史接纳。使用同一第一半开 owner，不从 child wall 投影选择父 label。`historicalPairs_trim_filter_eq_catalog:559` 给出

`historicalPairs(d,N,N,N^(19/96)).filter(trimmedRegion delta) = trimmedPrimePairs delta N`。

`historical_trimmed_sum_eq_catalog_arithmetic:583` 随即给原权重 sum 与 `trimmedArithmeticSaving delta N` 的精确相等。M 的 `tendsto_trimmedArithmeticSaving` 和 trim-integral passage 保持原证明；本批没有重新推 prime integral，也没有据 compact equality 宣称未修剪全域已比较。

旧网格覆盖使用 `HistoricalThirdCoarse` 真正全闭 ordered rectangle。`owner_selected_of_clearance:75` 用两道各至少 `2*meshStep` 的间隔和实际 stop 判据推出该 owner 被选；`unselected_owner_in_strips:100` 留下两个 order strips 与 first-stop strip。`owner_stop_of_historical_firstStop:129` 用同一第一半开 owner 的唯一性去掉后者。`candidate_original_firstStop:187` 从 P before-third candidate 的实际前两层历史推出 firstStop，不要求旧第三节点通过。因此 `candidate_unsupported_in_tail_or_order_strips:209` 对包括 restored 在内的真实候选保留完整 small-third/order alternatives。`exists_uniform_historical_owner_threshold:226` 给一个先于 e、N 及所有点的 m0，覆盖有给定间隔和 stop clearance 的 compact 源。它们仅定位支撑；没有把 strip 上的有限素数原子按 Lebesgue 零测直接删掉。

统一 rawLevel 供应不是假定端点近似。`exists_all_caps_ownCube_uniform_threshold:46` 固定 residualWindow `{(r,z):h≤z≤19/96, 2z≤r≤Theta}`，直接应用已有实际 quotient-compact lower-density supplier，得到一个 N0 统一全部后来 `lambda≤Theta`、实际 prime triples 与覆盖 cutoff 的 cap。gate 失败时 canonical lower profile 在 `s≤2` 为零，包含等号；没有额外扔掉 cube wall。`exists_actual_profile_cap_modulus:100` 只复用 canonical lower factor 的既有连续性定理，转换成 profile modulus。

最终 `exists_actual_coarse_rawLevel_to_endpoint_threshold:141` 的量词为：给 `h>0, eps>0`，先取 `delta>0` 与单一 `N0≥2`；随后对全部 OriginalData、全部偶 `N≥N0`、全部 `[h,19/96)` 实际 triples，若 `0<e<(3/256)/100`、`chi<e/10`、`3chi/2+2e≤delta` 且 actual selectedThird/secondGuard 成立，则供应 actual old first cube，并有

`|rawGatedMinus(N,N,rawLevel,p) - actualPrimeTupleOwnCubeMinus(N,N,v(log_N p1),p)| < eps`。

这里 `rawGatedMinus` 使用 literal strict product/own-cube gate、literal `rawLevel` 和 cap=N。`rawLevel=N^originalSeed` 是已存在的实际字典；`originalSeed_supported_interval` 给 `v(x)-(3chi/2+2e)≤seed≤v(x)-2e`。新证明将此区间、统一 N0 与 canonical modulus 合成误差，不以目标 density error 为前提。它并不把原 physical cap 改成 `N^v(x)`。该 interval 是所选 above-mu 源的现成较窄估计，不能与 source note 的全域 `4e+6chi` bound 混称同一声明。

去重覆盖 production、全部 source-only 批次及 ignored/hidden drafts。P 的 before-third 递归和 retained/restored lower 字典直接复用；O 的 actual secondStage、ancestor 稳定性与 small-third dispatch 直接复用；K 的 endpoint pair/trim 数据和 M 的 prime-integral limit 直接复用。新有限比较并未重做 P 的全候选枚举。

| 已核旧源 | 使用边界 |
|---|---|
| `.lake/proof-continuation/source-reviews/drafts/20261028-Coefficient-Sol6-AboveMuFallback-Phase5/P5OriginalAboveMuFallbackPhysicalCoefficient.lean` | 旧第三 parity 版本只作去重检查，不导入、不复活为 lower 源。 |
| `.lake/proof-continuation/source-reviews/drafts/20261028-Coefficient-Sol6-ThirdLowerParity-Phase7/P5OriginalAboveMuThirdLowerPhysicalCoefficient.lean` | corrected lower-parity 几何由既有依赖链复用；second region/cube 与 raised cap 几何不再重证。 |
| `.lake/proof-continuation/source-reviews/drafts/20261028-Coefficient-Sol6-ThirdAdmissibility-Phase8/P5OriginalAboveMuThirdRaisedAdmission.lean` | 已有第三 fallback admission；不是本批第二 source 的 pair 转换，未复制该证明。 |
| `ImbalancedChen/ActualExtendedThirdDyadicCoverage.lean` 等 dyadic extended-third 源 | 其 policy 只要求 ordered portions，与 actual historical 全矩形 policy 不同，未借它的覆盖/retained region/convergence替换 actual 源。只复用独立于这些选择的 canonical cap-kernel modulus。 |
| Q22 `buffered_policy` | 有限 strictly buffered 新 rank2/rank3 cap 与其 admission walls 由 Q22 负责；本批旧网格 coverage 不构造另一套新 cap 表，也不重复计其 wall payment。 |

剩余工作具体为以下各项；三份新源码均未假定这些结论成立。

1. **actual coarseRow 的完整加权总误差。** 把有限 `coarseRow` 在实际候选 carrier 上逐项识别为带原 mass 的 gated lower-density 差，并在固定 h 上统一求和；保持 target deletion、所有 occurrence、old-rejected gates 与 cap=N。当前 rawLevel theorem 是真实 compact summand estimate，没有已写出的 normalized `Σ coarseRow=o(1)` 或相应 allowance 结论。
2. **未选 order strips 的实际质量。** 现有定位必须接实际完整 `omittedRow` residual 的算术质量估计及共同墙族参数，保留边界 prime atoms。点的位置趋近 proper walls 不能自行证明其加权 source 质量趋零；P 的局部 proper-wall supplier 也还不是这里整项的已完成调用与总账。
3. **disabled-small-third 的非紧 tail。** `p3<N^omega` 的完整 omission 包含端点 residual 差，需要原 large-s cancellation/tail envelope及实际算术求和。source note 198–205 给 `18h/(u-h)^2*(log(rho0/h)^2+2log(rho0/h)+2)→0` 的数学路线；本批未将它证明为该有限 source 的统一界，不能以裸 Euler/harmonic mass 或 actual change=0 支付。
4. **未修剪的历史 pair complement。** cleared compact Finset equality 已消；尚需把全 `historicalPairs` 中 guard 成立的余部与所取 compact 源作合法比较或绝对误差控制。不能无证断言有限 actual residual difference 逐点非负，再由 M 正积分与 trim exhaustion推出完整历史 saving 下界。
5. **同一完整历史的选择与支出。** 上述 h、old buffers/mesh、Q22 new buffered caps、higher actions、omega/J0、beta/compiler 参数与最终 N0 仍需放入一个共同 pre-N schedule，并接同一 physical rho。任意 T 的有限恒等式允许保留同一 terminal test；这里 actual ordinary-density 字典专用于 T=1，不等于已经供给 beta-attached density。原第四 row/licence data、所有 87 分支、四正减 22 项、完整第三 tail 只替换一次仍须各自供应。已有 finite-third approximation 消耗 `u_d/4`，其余 density 只余 `3u_d/4`，compiler 的 `u_c` 独立；本批没有声称新支出或两笔总额已付。

困难分类：(2) 本批补出的窄内容是遗漏但可直接推导的有限 source conversion、actual old-grid coverage、compact carrier equality 与 rawLevel uniformity；没有把相同目标估计换成假设。(1) 全部 Lean elaboration/API 仍未执行，仅做声明、namespace、类型及静态证明步骤核对。(3) 尚未闭合的 weighted/tail/common-history 供应是明确的剩余数学义务；本次没有给出原稿反例，也没有据当前形式模型不足认定实质数学缺口。

独立 q30 已读三份源码并给上述窄内容正向静态意见，尤其确认 compact carrier 已消、两个差额的符号、rank3 lower/rank2 upper 及统一所有 lambda 的阈值；完整 catalog5 与 All22 保持 HOLD。审查文件由 q30 独占维护于 `docs/source-only/20261102-resume-30q/reviews/q30_review_history_final.md`。该意见不是编译或 kernel 验收。

| 最终新源码 | 行数 | 原始 SHA256 |
|---|---:|---|
| `P4ACatalogFiveHistoricalCoverage.lean` | 253 | `763f57ab4ec08ac2e58bd4625f2179d2b674bdf999f1024d26b1ba387698e4c8` |
| `P4ACatalogFiveActualPairDecomposition.lean` | 598 | `521332733d612670c3ff434a7fd842efb7fd0cddc3076753270c002abf2ca6be` |
| `P4ACatalogFiveCoarseResidualUniformity.lean` | 218 | `1c11cdfd3fb42e6e9184573a5ff7ca3136ccfb2cdb7eb0d2453168bd53e0c01a` |

仅进行文本读取、源码编辑、静态检索与原始字节 hash/metadata 检查。没有 Lean/Lake/compiler、CI、proof-guard evaluation、数值重放、Git 操作、旧源修改、子代或 import materialization；没有新增 axiom、sorry、admit、native_decide、#eval 或 #check。唯一写入范围为本任务目录。
