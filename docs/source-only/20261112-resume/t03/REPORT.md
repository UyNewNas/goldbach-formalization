# 早期三槽付款与 P4 源码对照

原十二源已在 `2798513f25c982c151b878ce36c08d28af12bc6c` 发表。T09 独立审过其数学，报告 SHA256 为 `6dfaa58ce5126d829870574e3c4adf8601509bbf0ea332029924dfa8dc4a8cc5`，原件白名单为 `23211f4b06d4c36953ec897014bfb03b21e45e065d99ea1ee4395346d98cca2a`。本轮逐项回读原登记的 12 份源码、15 个直接外部导入、10 个原始输入、18 份依赖记录及原报告，检查了字节数、SHA256 和 Git blob。原登记 `1f4754e608bc9682684401418ba5e83a0d678636cb4246c67a3aa1eea549eabb` 与末端源 `141d73f387f81246ecd2770c7a9322249a50919cc052cae770e96dd805720027` 维持原字节。

## 对应原稿、参数和实际策略

| `currentUpperEighteenGains` 下标 | 真实原项 | 原标量下界 |
| --- | --- | --- |
| 0 | 较强第四前缀全替换 | `10601625247768616959055 / 2^78` |
| 1 | 旧第五的 143 个原始块，64 子块预算在此使用一次 | `3037921066812732539869 / 2^78` |
| 2 | 新增第五的 94 个原始 NPZ | `1648717268323516459667 / 2^80` |

第四项使用 `fourth-prefix-stronger-refinement.tex` 第 19、158、190 行的实际支撑、204800 格和原 floor。第五项使用 `imbalanced-chen-transfer.tex` 第 10774、10790 行的 `rank5-exact-density` 和 `rank5-density-gain`。每个第五候选分别在旧、新层高上重测自己的立方截断。跨过旧截断后恢复的词也进入同一有符号差。下标 4、5 是另付的高区两个槽。

`EarlyHistoricalFloors.split` 第 24 行给出旧第三树 `common3` 至合并第五 `policy5(data e q a)` 的精确分解，包含真实第四、旧第五和新第五。`historical_payment` 将三个原 floor 一起付在这个未量化的旧树上。最终比较则以 `d=data e q a`、`cap=N`、普通筛区间 `(0,N^(19/96))` 固定

```text
lowerEarly = normalize N (rawRoot (fresh d omega N) N
               − rawRoot (dispatch N (fresh d omega N) (orderedFifth n d omega N)) N)
```

`EarlyFiniteStages.actual_dispatch` 第 90 行在所有高区词逐词保留相同的 `fresh`。低区使用实际全有序第三层和实际有限第四、第五层。`signed_lower_early` 第 127 行取新树准入的全部四元组及这些前沿的全部下一候选五元组。`EarlyHistoricalSums.unrounded_sums` 取旧第三树的两个相应载体。两个分解都保留权重 `∏i (pᵢ−1)⁻¹`。

两树只在有实际行贡献处使用 owner 相等。第四行满足 `q=256k`、`k>0`、`4e+e/20≤1/3200`、格宽至多 `e/20`、`omega≤a≤3/200`。每个原格单位含 `3k` 个细格，删去 (N) 的素因子后实际素数无法恰落原有理上端面。第五行用旧、新行的真实 eligibility 取得与历史相同的第三层 owner。第四坐标全体至少 `3/200`，第五坐标全体至少 `1/400`。真实第三层读取一致后，第一、第二和偶第四层的读取给出 `carrier4_on_owner`、`carrier5_on_owner`。在无有效行的词上，两树各自的局部差恰为零。这一步允许其原始载体不同。

对实际受保护的层高，单端点移动至多 `2*width n`。第四的 PLUS 使用从商一开始的合法区间，第五的 MINUS 在商二处取零并连续。第五的新旧两个截断都参与比较。`EarlySumComparison.same_target` 第 74 行将误差界在 `u*M4+2*u*M5`，其中两项是删去目标因子的固定紧盒素数质量。两个质量上界先于 (n) 选择。由 `original_low_early_payment`，每个正容差先给 (n₀)，每个 (n≥n₀) 再给 (E>0)，每个正有理 (e<E) 和 (0<a≤1/800) 再取 (q₀)。所有足够大的正倍数 (q=256k) 都能满足任意预定的网格下界。有一个 (N₀≥2) 对全部 `omega≤a` 和所有后续偶 (N) 统一有效。`cofinal_actual_early_defect` 选一个这样的 (q)，给出实际 `lowerEarlyDefect<eps`。

## P4 已发表内容的交集

按 `eea9486f7b101d484e2938e97499c1d77cc1a67a` 的树回读。P4 的十九槽与 T03 的前三槽共用 `P4AOriginalFiniteAll22RawLedger`，blob `88a37861a9d5bdfaec4cdb34196cc0fe5f91afe2`。P4 交接中记载的 404 对应当时未能读取的早期登记。根在本轮已经发表该原件。

| P4 源及 Git blob | 重叠与适用域 |
| --- | --- |
| `FiniteAll22EarlyInactive` · `b37acee523c6fc53a56835a868011e8e74dc1cda` | `base_current/common_current_below` 与十二源中 `base_is_fresh/low_common` 对应。它另给出任意子树测试下 inactive 前沿差为零，并把 `lowerEarly` 化为 `normalize(−rawChange 4)`。实际占用的 4/5 元组跨两个载体的重标记及原数值下界由十二源接上。 |
| `FiniteFifthCompactProfile` · `5a21bdc2c8ee514bbf7a8d6a041020126aafcdd6` | `exists_actual_levels_close_threshold` 适用任意维度 (k+1)、正的坐标下端和固定层高区间。取 (k=4)、坐标 `[1/400,19/96)`、层高 `[0,1]` 再用格宽趋零，即可恢复十二源的五维 `compact_fifth_shift`。同一连续性估计只需支付一次。 |
| `OrderedFifthRoundingResidual` · `5de744ed614b0b9575d25bbd3d61caa273b089d5` | `cap5_eq_protect` 与 `cap5_as_protect` 为同一嵌套保护恒等式。其末端在 `0<e≤1/384`、格宽至多 `e/2` 及正的五维坐标下端上，比较同一 `current` 的一个未量化第五端点与实际保护端点。十二源的总差同时使用第五求和中继承的第四端点及真正四维 PLUS。 |
| `FiniteAll22Nineteen` · `abadf4d9fbbec16085deb732f4e3388e35500218` 和 `FiniteAll22EarlyDefectCounting` · `fb3aa5371d57b599fac9726603aaf3d179dd38db` | 分别给原下标 3 至 21 的付款及同一有限系数的密度、支持和计数。旧右端保留 `lowerEarlyDefect`。T01 新定理直接使用后一计数端点，在 (a) 选好后取共尾整倍数 (q)。 |

## 三个尚未上传的 P4 原件

本地 `unuploaded/RECOVERED_IDENTITIES.json` 和实际字节逐件吻合。仅用于重叠核对。

| 原件 | SHA256 | 独立核对结果 |
| --- | --- | --- |
| `P4AOriginalCommonThirdFifthTelescope.lean`，44 行 | `36cf2231f7aaac92a5af94a3a62df1320c242bf235be05579b51c177f3718240` | 第 19 行对任意 (e,q,a,N) 且 (1≤N) 的结论，在展开 T03 的 `gain` 后与 `EarlyHistoricalFloors.split` 相同。两者都消费已证的第四有符号修正，两个表达给同一笔历史分解。 |
| `P4AOriginalNewFifthThirdOwner.lean`，180 行 | `5bc470505d33cd9ef661920d776814fd0f39689e31d981edd288a0630d235282` | 第 138 行在 (e≥0, omega≤a, N>1)、任意 `cap`、任意五个正整数上，证明旧、新第五两行簿的未量化 `new−old` 增量在 `current` 与历史第三树相等。落入新标签时用双方旧 owner，标签外两本簿的上确界在同一根相等。该结论在点和参数上较广，比较的量与 T03 实际受保护的 `fifth−fourth` 前沿不同。 |
| `P4AOriginalFourthLowSourceSupport.lean`，72 行 | `008c580616d4563fb480a0320797c74ac409ee6a4665984c30c1f0827376f771` | 第 23、46 行给历史第四 PLUS 在 (t₀>μ) 逐项为零及旧求和的低区过滤恒等式。其一般参数域可供旧历史调用。对新树实际准入所需的第四格 owner、跨载体等价和量化误差已由十二源给出。 |

三个原件都没有成为本次安装选择或 T01 合流的依赖。本轮没有上传它们，也没有重写对应的三个定理。P1 的 `a023ae055d3d90738f6965a2848266aa13089faf` 中 `Full87SixthBothInvoice`，blob `fe848722381b301e3d044a284aad29cb4fa1909e`，处理另一对策略的高模数 stopped 账单。它在原 `epsilon≤1/500`、(N>1)、`X≥N^(3/5)` 等假设下，消去第五均准入后的第六 BOTH 型零项，保留第五或第六单侧准入项。该账单与这里普通筛的正第四、负第五之差是两个对象。

## 本轮选择与剩余验证

原十二源安装时唯二新增改动是在 `EarlyTupleCarriers` 第 6 行和 `EarlyTupleComparison` 第 5 行各加一个 `List` 作用域，使三处 `<+` 承接锁定 Lean 核心 `src/Init/Data/List/Basic.lean` 第 1110 行的 `List.Sublist` 记号。安装变体的完整前后 SHA 和 blob 在 `EARLY_LIST_SCOPE.json`，SHA256 为 `947e219bd4fbd7f8b4000c0827c0dff6d4c3b24d44499f9ee5a7584c61c2e73c`。补丁 `3b3031443bdbb6aa34dab65fe58b07c62ad8363e389f1a684e7f533d736582b3` 仅加两个记号。T09 已核补丁上下文及两份后像，安装独审 `04b4ca5f80f767956a20c197fe2e94c83289e6da6c6ac715ebe4471a3522c848`。继续沿用 FullPolicy 的公开作用域修订 `01f09fb673c06fb7950c3eff48dbe9dc815c9dc983afe6f61341a171475a2324` 与原 R17 选择。

T01 合流源 `3e4ef38c9abc25e35ef446f52ed9e4b2bba112743445e19f64937e7eeaa9a604` 已另作独审。它在同一个 (q) 上只选一次 `beta,k`，以两份 `eta/2` 消去同 (N) 的实际 early defect，保留真实预筛修正、编译费、模数支持、完整 `realPhysicalDistributionError b N T Q rho` 和有限计数损失。真实分布误差及完整 `hUpper` 仍待证明。此次仅核源码、不可变 Git 对象和字节指纹，尚无 Lean kernel、传递公理或有限守卫执行结果。[合流独审](T01_COFINAL_COEFFICIENT_REVIEW.md) · [合流精确白名单](T01_COFINAL_COEFFICIENT_ALLOWLIST.json)
