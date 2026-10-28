# lower_tail E：真实 same-Q 负子项修正

本批仅写 `20261028-resume-30e/lower_tail/`。没有编译、Lean/lake、数值 replay、额度检查或子代理；全部为 source-only，`compiled=false`、`formal_credit=0`。原始 L5/L6/common approximation 总任务仍 `task_complete=false`。本批完成的窄步是：从原始 21 项真实 prime-label sifted counts 构造并证明带符号负子项计数修正，而非再保留一个未支付的 H248 densityDefect。

原稿依据为 `manuscript-body.tex` 790–877 行，尤其同一 `Theta_Q`、正 marked family、实际子项保持同 Q/全部 square/物理 ceiling、alpha 不重置，以及原两步反馈公式。原稿 SHA 为 `ee6aecc164cc59f2d1fed1ad9e48f18f98472ab1d77ab425d53d93bc41ce56bd`。Scope 按 SourceReview-V2；未发现并未声称新的原稿反例。

`P2EnhancedNegativeChildRosser.lean` 直接使用生产 `ActualSmallRosser` 的真实 lowerWeight。对三条原负窗 `[a,f)`、`[a,c)`、`[a,e)`，保持 `a=(Q/d)^(50/227)`，old mask **d*N**，actual level **Q/(d*p)**，物理 AP 模数 **d*p*k**。原窗是 `primeWindow N`，所以没有偷偷删除 `p|d` 的行。由实际 prime 参数推出合法 level；原 source 与 quotient 在 p>=a 时相等；有限接收者/除数 Fubini 和已存在 Rosser sandwich 给出

`childEstimator <= sourceSieveCount N (d*p) (d*N) a`。

实际支持还导出 k 与 d*p、N 互素以及完整物理模数 `<Q`，而非把 residual-wellness 当作新假设。原 prime receiver 为 `[0,N]` 中真实素数，不删中心、不删端点、不删零/单位 quotient。

同一个 coefficient 有两套精确均值拆分，两者严格区分。

* `childMean` 是 guarded `li(N)/phi(d*p*k)` 的 **AP 模型均值**。`childMean_eq_guarded_residual_density` 将其严格分解成 prefix factor 乘实际 ordinary residual density；没有 H248。
* `childFiniteCoprimeMean` 使用独立有限 prime population 中 `ell.Coprime (d*p*k)` 的真实质量除以 `phi(d*p*k)`，并保留实际 residue-class coprime guard。其 signed AP remainder 仍是相同物理 AP count 减该有限均值。

两者都有 `estimator = mean + signed remainder`；`childFiniteMeanShift` 明确给有限 population mean 与 li-model 的差额，并在 remainder 中以相反符号出现。本批没有将任一 remainder 或该 shift 声称为 `o(Theta)`。

`P2EnhancedTwentyOneChildCorrection.lean` 保持生产 `quotientLocal` 的标量与原始参数。定义的 correction 是

`三负实际 AP-model mean + 三负 signed remainder - 两原正 pair counts - 全 quotientSwitched`。

`signedChildCorrection_eq_finite_coprime_split` 给完全相同的有限 exact-coprime-population 版本。`weightedQuotient_le_baseline_sub_correction` 的关键方向来自刚证明的负项 lower estimator，而不是假设一个增强均值。生产 `twentyOne_source_comparison` 已有的 collision/bad-prime theta payment 随后给

`5*Phi(11/5) + signedChildCorrection <= 4*Phi(227/50) + Phi(353/100) + epsilon*Theta_Q`。

阈值在 N、Q、D、sigma 之前选择。小 N 的有限版本保留原碰撞和 bad-prime 项。same Q、同 sigma、同 Theta、实际 cutoffs 与 old masks 全部来自原 source。`quotientSwitched` 是原 Gamma7–21 全 marked-word 字典，包括重复 occurrence、各 arity、unit quotient；没有将其替换成空 exporter 或尚未证明相等的 triple-only bank。

`P2EnhancedNegativeChildPhysicalSupport.lean` 是额外的单向物理支持桥。它消费 lower_square 独立冻结的 `P2OriginalNegativeSingleSameQSupport.lean`，raw SHA `589c3cd5bb389e7e9da4bddf0f116c5902ce33def2a76292db35c273a1890b99`。两边 actual coefficient 用 `rfl` 相等；因此本文件真实 count coefficient 非零时，可从实际 old tagged prefix 的 gates 继承完整 full/selected-complement squares、原 selected 标签、完整 product 和同 Q 上界。没有从 candidate policy 推出 adopted L5/L6 source bank。

安装顺序：先将本目录 `P2EnhancedNegativeChildRosser.lean` 置于同名 `ImbalancedChen/`，再安装 `P2EnhancedTwentyOneChildCorrection.lean`。物理支持桥还需要独立冻结的 E lower_square 文件及它的 A/B source-only 前驱；其精确路径、hash 和既有 registry 已登记，不能假称这些前驱现在已在生产路径。生产/外部库关键源均有精确 raw hash；Wu 源的 Windows package 是不可读 Linux symlink，读取与哈希使用 WSL 的真实 research/wu2008 路径。

冻结源码：

* `P2EnhancedNegativeChildRosser.lean` — `3388ccb72a54ef7537b7d071cd3ab2da0b58cbddf8f35d2238d735a5b17de82b`。
* `P2EnhancedTwentyOneChildCorrection.lean` — `fcb1097f8d5ba58346ec03072a5207a9380744dc8dc85b2cc11a44b9006e6e69`。
* `P2EnhancedNegativeChildPhysicalSupport.lean` — `127e93dd1f0f7ebdb28576c9897bc850942c97bb9ba7c8969653288db492c6bb`。

仍 OPEN：全实际 family 上同系数 signed AP 余项和 finite-to-li shift 的统一小误差；负子项真实 ordinary/enhanced 解析均值；两正 pair 与全 marked switched source 的 actual positive-K licence/cost；原 immutable-old action count induction、alpha/causal-history/retained-source 的整体绑定；实际 adopted L5/L6 及 U10/U11 同 mask、固定 mesh/compiler enlargement、fallback 计数与最终 H248 成本的衔接；原始共同有限 dyadic approximation。C/D 的 clamp/fallback/ordinary-vs-enhanced distinction 完整冻结未动。本批既没有把 ordinary rho 密度改成 H248，也没有完成 H248 增强 count bound。
