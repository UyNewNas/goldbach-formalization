# t25 — H430 O/P 独立关键复核

**结论：HOLD。** `h430_smooth_causal_boxes`、`h430_frozen_q` 的原始完整目标及 `P5.6.eight_suppliers` 仍未闭合。最终 P10、P11 的下述局部增量均为 **PASS（仅静态源码范围）**；不表示 Lean elaboration、kernel 验证、安装或原稿完整证明通过。

`review_complete=true; compiled=false; kernel_verified=false; formal_credit=0; full_target=OPEN; finite_guards=UNEVALUATED; ready_to_install=false`。

审查者：`/root/t25_review_h430`。先读完 O 六份源码，再审两位作者稳定 P 候选、报告和登记。只写本审查文件；未改作者文件，未执行 Lean/lake、编译器、有限证明 guard、数值 replay、Git 或子代理。JSON 解析、声明行号和 SHA256 核对均仅属元数据检查。

## 范围及最终字节

以下路径以仓库 `E:/timot/Documents/FilesForGPT/Myath/goldbach-proof-continuation` 为根。`O`、`P`、`M` 分别指 `docs/source-only/20261102-resume-30o`、`docs/source-only/20261102-resume-30p`、`docs/source-only/20261102-resume-30m`。

| 文件 | SHA256 |
| --- | --- |
| O/h430_smooth_causal_boxes/Part5OriginalH430CellMeasurability.lean | `8c5d0d4f4c817c8b16dccfaae4b0d2f62c633db099e1a892da1a8303d5db7072` |
| O/h430_smooth_causal_boxes/Part5OriginalH430NativeQueryPaths.lean | `118c03b4a44068a8cbb696f39699d12ff83b84d95a46f6d77b07b109f440cdeb` |
| O/h430_smooth_causal_boxes/Part5OriginalH430RootGateObstruction.lean | `d2897afbf9efc91f35a3d911dce5e826578daa5b967cf90ff49d37c74633f72b` |
| O/h430_frozen_q/Part5OriginalH430FrozenPerturbation.lean | `d11f4647a52c907681b8223f7e06b1f242c843d488366919d1319b07296142d1` |
| O/h430_frozen_q/Part5OriginalH430PhysicalMassPerturbation.lean | `42848eedf3346f1c7105d8734c2fa7273cab8eab9d80c50a076d85ed92600199` |
| O/h430_frozen_q/Part5OriginalH430FrozenRootMass.lean | `04f63c5ae0b6fab3a60e91c34abaf7949f8cdf104c070f5f941b3c4e0cd8bdd1` |
| P/h430_smooth_causal_boxes/Part5OriginalH430MovingBuchstabAtoms.lean | `e315a51795bd9b3d77232857a1f743b67e223959696e69f78f272fbf93f6c873` |
| P/h430_frozen_q/Part5OriginalH430FrozenTableRootMass.lean | `6f96860efb43e4cd7f6278baecc4a3b6765e7e02b8dfe7a694f2b7aa2d7c5725` |
| P/h430_smooth_causal_boxes/REPORT.md | `619729a161b27599a01ca26e5aae6e2473546657220ebf098fa1fcc3f9bcebe7` |
| P/h430_smooth_causal_boxes/REGISTRY.json | `ecfc7001f874ed310aefe0da35d112df55b6a5a5d817b4a1929fb9044be9bd41` |
| P/h430_frozen_q/REPORT.md | `e439211e8a42a660b2eb9cd27c7044cdf607e84f2bfb991efcf22e1ab084a161` |
| P/h430_frozen_q/REGISTRY.json | `2bebb99b6896b153fa8c0c101b337c8e7698d6ff906d2f439d46eead20b32146` |

P10 登记的 24 个不同路径（34 次 pin 出现）的 SHA256/字节数全部匹配；25 个新声明及其列出的复用声明行号匹配。P11 登记的 16 个 path/hash 项全部匹配，其 14 个重点声明行号已核对。O 两目录原本没有各自 REPORT/REGISTRY，不能继承不存在的完工声明。

M 四个直接背景源的当前哈希与既有 pin 一致：PhysicalRoots `560c588ed72d45ba8d8d2b28ba5b2b964fdc69a8acf27b066d835e702c4759be`；FrozenRootRefinement `d05ebfcc10e8dde12560e87d99a9c47082c69995184e4aa2689bbec9fd92f8f1`；AbsoluteQueries `66f3223b1d05776561349063a48e00cd0cd90b54be2081c676565b729bd47b13`；GeometricWalls `2732c16e9b1c0b6d7d07cdbe59ae4073271dd8e639c38aacd609450aee966284`。M/N 已有报告和限域亦已读取。

## 原稿先行核对

`../chen-imbalanced-semiprimes/paper/source/manuscript-body.tex` 的 808–895 行首先读完，SHA256 为 `ee6aecc164cc59f2d1fed1ad9e48f18f98472ab1d77ab425d53d93bc41ce56bd`，与 BRIEF 相符。

- 808–817：同一 total Q，真实 residual 和 alpha 更新；alpha 不能重置为 2。
- 839–855：三个 singleton、四个 good pair 域；`2v<1`、`v+2u<1`；坏 D5 只作 positive product cost；unit surfaces 留在 switched mass 内。
- 857–865：只读前代，替代方案取最大而非相加，crossing cells 用 closed support minima；430 为 simultaneous seed-only history，248/312 不是生成输入。
- 867–877：先在最终 reserve 中选 delta，再选一个共同嵌套有限 refinement；norm12、root norm7/2、`(12^441-1)/11`、depth440 和 `101^-440` 固定正下界不得改变；零质量片保持绝对误差。
- 887–895：H430 仅给 U3/U4；`max(2,L/a)` 的 clamp 是正测度状态，不能当成 proper null wall。

另核原始模块 `global-chen-lower-completion-20261010.txt`，SHA256 `8597fd1dc01d3fc49e5b31d28afeab3cf48e88ae23908fb6777a1c23f5b360e5`，特别是 175–197、223–237、239–289；`distribution-coefficient-completion-20261010.txt`，SHA256 `a6cfa86f625242527df3ba485a7e86867b84e289bca651c0e8b942be36f0fc69`，特别是 95–139、227–244；`final-lower-cross-review-20261010.txt`，SHA256 `4ca0d6799ff2b9b8616e10ec5ed6c4bae0d881bf4ece09165bc336e4a755ee48`，特别是 118–168。

## sourceRoot / full square / U3 tail：精确分类

**PASS：O 的否定命题作为现有源码模型的命题成立；HOLD：它不能代替原稿反例或原稿许可。**

1. M `PhysicalRoots:40–46` 把外部选定根指数 `t` 放入唯一 selected slot，total 指数为 `t+R(t)`。生产源 `P2EnhancedLowerPhysicalNode:43–52` 的 `fullGates` 用 `n.total` 对整个 `word` 测试平方。因此 O `RootGateObstruction:26–30` 得到精确等价 `fullGates(sourceRoot) ↔ t≤R(t)`，即根处 `2t≤Q_exponent`。
2. U3 尾部 `t≥57/224>1/4`，`R(t)=1/2-t-tau`，`tau≥0`。根测试遂要求 `2t≤1/2-tau`，不可能。O `:36–43` 证明此否定；`:45–66` 证明向下冻结 total 不能修复；`:70–88` 证明追加任何 Program 仍保留失败的原始测试；`:92–100` 给出包含在原 rootBand 内的非空开区间 `(57/224,1/3)`。这不是可扔掉的端点或 proper wall。
3. 原始 completion 模块 `184–189` **区分 enhanced 状态与 classical complete level below half**，并区分物理 cap lambda 和可能更大的解析 support cover `ell_aux`；`254–256` 明确 U3 tail 使用 half-level 的下极限。distribution 模块 `97–107` 的 full/selected squares 右端是 `ell_aux`，`234–237` 另记 classical buffered complete level/BV 路线。现有 `PhysicalNode.fullGates` 一概用物理 total，且该根模型没有表达此 classical/enhanced 来源区分。
4. 因而这首先是**来源建模入口过强/缺少来源字典**，超出单纯 Lean 语法或 tactic 修补，却未证明原稿数学不成立。正确补法须为 classical 尾部及 enhanced cover 给出实际算术许可和历史关联；不能直接删除根平方，也不能把 `ell_aux` 写回物理 residual/alpha 来绕过失败。
5. O/M 的 residual floor 并不因此变成假命题。`Member`（FinitePhysicalGraph:83–90）测试新 local transitions，而 `realize_gates_alpha:244–257` 另要求原根 `fullGates`。现有 floor 可以在其真实 `Member` 范围成立；它仍不供应缺失的全历史/计数许可。

结论分类：局部模型障碍已经精确定位；classical/enhanced/source-history 的修正是尚待证明的来源转换。不能把该障碍写成“真正原稿反例”。原稿所断言的完整共同算术构造仍是实质性未完成义务，不能仅以“有限深度”或“表达问题”消除。

## O 的可复用局部范围

**PASS（静态局部范围）**：未发现最终 O 六文件中可确定的新增局部数学错误；不继承任何编译信用。

- CellMeasurability `:33,80,135,160` 给 common/full/root fibres 及 frozenLevel 的可测性。可测有限标签本身不是 smooth prime-box 实现。
- NativeQueryPaths `:31–54` 保留 W1/W2 标量和 labelled component lists；`:80–130` 的物理 query 恒等式真实，但 Buchstab fixed-domain 对应需要 `StartMatches`；`:133–210` 保留 native prime arity、padding、same Q 和 selected root。`:214–224` 的 `actual_ancestor_choice` 是 rank1 原根特例；完整祖先因果族仍须应用一般 prefix 定理及真实来源关联。`:228–239` 记录 Program/query occurrence，不产生许可的算术族。
- FrozenPerturbation `:100–203` 在 **同一 code、同一物理追加坐标** 比较 residual、reciprocal、alpha 和 normalized coordinate；其正分母来自 frozen `Member` 与 depth≤440。它没有证明 ideal/frozen `Member` 指示函数相同或其差的质量趋零。`:281–294` 精确保留 clamp；`:296–319` 控制根 query 改变量。
- PhysicalMassPerturbation `:26–96` 的权重为 `4/(word.prod*residual)`，并给 singleton/pair/Buchstab Jacobian 恒等式；`:100–119` 后代界仍带实际前缀倒积。该连续模型不是 `C(BN)/phi(B)` 算术质量律或 marked-family count licence。
- FrozenRootMass `:63–98` 先证明两个 root 权重可积再比较积分；`:102–132` 取实际正 `finiteTau n` 并得未加表权的根误差趋零；`:134–184` 仅在完整 clamp 区给表权误差。后者原样保留 `min(floorValue H430Numerators 49, floorValue H430Numerators 50)`。

## P10 局部增量

**PASS（静态局部范围）**：`Part5OriginalH430MovingBuchstabAtoms.lean` 最终哈希见上。

- `actual_child_moving_domain:67`、`actual_child_moving_atom:95`、`occurrence_moving_atom_exact:112` 用实际父 `n.argument` 定义 moving Buchstab 域，确实消去 O 的 `StartMatches` 入口；仍只要求字面 `LocalDomain`。这些是定义到定义的实际对应，不假设 smooth realization 或目标误差。
- `startAtomDensity_integrable:133`、`startAbsoluteError_integrable:187` 先证可积；`:159–182` 用两个起点间**闭区间**的 indicator 支配真实核差；`:194–209` 积分后得到 `L1≤|a-c|`；`:213,226` 得上下实际 moving/fixed start 的误差界。`buchstabKernel=1/max(1,w)` 及其≤1界来自实际生产源。
- `upper_constant_start_exact:236` 保留 max-two 起点的整块常值区域和每个 closed atom。`lower_start_two_open_strip:247` 只说明 moving lower start2 的 `(1,51/50)` 不在旧 fixed primitive 域，未断言该区间都是获许可路径，也不是原稿反例。
- 可测性是**每个固定父状态**的可测性；误差是一维 normalized Buchstab 误差。固定表网格仍为 `1/50`，细化其他标签不能令任意父参数到该网格的距离趋零。因此没有由本文件得到任意 delta 的全父族逼近或物理父积分支付；最终 REPORT/REGISTRY 已明确这一点。

首轮读到的区间长度 proof 使用 `max_sub_min_eq_abs` 后接相反方向的绝对值；实际 Mathlib `Algebra/Order/Group/Unbundled/Abs.lean:269,276` 的 to_additive 给出 prime/nonprime 两个不同方向。作者最终在 `:202–207` 改为 `le_total` 两分支并使用 `volume_real_Icc_of_le`，已重新静态核对；此问题属于 class1 表达/API，未改数学命题。旧来源声明行号也已在作者 REPORT/REGISTRY 更正。审查者没有改作者文件。

## P11 局部增量

**PASS（静态局部范围）**：`Part5OriginalH430FrozenTableRootMass.lean` 最终哈希见上。

- `proper_root_fibre:44–79` 从原始两个 main 仿射分支和 U3 tail 得到非clamp query 值 c 的 fibre 至多落在 `1-2*a*c`、`(57/64-a*c)*2/5`、`1/2-a*c` 三点。`:87–103` 只移除有限 proper knot fibres；没有把整个 query=2 的 preimage 判零。
- `ideal_clamp_preserved:107–114` 对两根精确保留 ideal clamp。原 U3 正测度区 `[833/2500,1/3)` 不被删除，2 处相邻值最小值仍由原 `upperFloor` 的 closed knot atom 决定。
- `eventually_upperFloor_eq:141–166` 用 201 个 knot 两侧比较的最终稳定性，逐一保持 finite closed atom membership；不假设 H430 连续、单调或其数值正确。`:168–205` 将真实 root query 收敛与 clamp 恒等式合并，以 `2*floorBound` 作可积支配，得 table discrepancy 趋零。DCT 的外层 norm 已明确处理。
- `:222–240` 分别证明 ideal/frozen 表权根质量可积；`rootTableAbsoluteError_bound:248–297` 正确拆为 `floorBound*rootAbsoluteError + weightEnvelope*tableDiscrepancy`；`:299–319` 推出实际 H430 correction mass 的 L1 收敛和两积分差界。
- `exists_common_root_table_precision:324–333` 是对两个 roots 同时选一个 n，并取正 `finiteTau n=min(1/12,1/(n+1))`，在算术 N 前完成。它既不声称独立二参数 product-filter 极限，也不声称所有441代后代的共同选择。

这补上的是 class2 可补省略推导：非clamp **根 H430 correction 项**的表权稳定性。完整 `(upperAmplitude-H430)*branchWeight` 尚差 continuous amplitude 项的正式组合；移动后代 admission、后代 knot/gate pullbacks 和真实算术 normalization 均未在此证明。最终报告准确保留这些界限。

## 仍须 HOLD 的完整链与量词

1. 先有最终 reserve，再选 delta，使 `(7/2)*delta*(12^441-1)/11` 落入 reserve；随后构造一套共同嵌套、祖先 cap 只依赖自身 prefix 的有限 smooth 算术族，并固定 tau/levels，最后才让 N 增大。P11 的两根共同 n 与 P10 的每父局部 strip 界没有给出该全链量词。
2. M `AbsoluteQueries:257–272` 的 `Fin441×Primitive×FloorAtom`、M `GeometricWalls:143–165` 的 summed absolute errors，不能自动成为实际路径的 `localBudget`。O/P 加入了 `GraphVertex`/`occurrenceInput` 对应，但没有提供 immutable430 的源历史、所有权重/基项/标量、每代旧状态读取及预算恒等式。生产 `RenewalFiniteErrorPropagationP5:239–253` 仍需要这些实际 `hw/hmass/hlocal` 供应。
3. 理想/冻结后代 `Member` 域的 symmetric-difference 质量、真实 prefix 密度下的 proper-wall 误差、identity/inherit 等式片的精确保留尚缺；仅凭逐点 residual 收敛不能把全部边界宣布零测。
4. D5-bad 与 Gamma9–21 是 positive switched bases，不能改作普通 feedback edges。其 smooth 外逼近、实际 source dictionary、unit pieces、multiplicities 和固定 cutoff 许可仍须供应。普通 `StepShape` 的 floor 不能替代所有 switched leaves 的来源证明。
5. 本次 O/P 包没有供应完整 smooth 族与真实 `Theta_Q` 正质量渐近的组合，也没有供应最终 H430 marked-family licence、analytic seed、signed sharp AP、switched cost licence 或 U3/U4 改进计数定理。P5.6 以及依赖这些供应的终端不能因本次局部结果转为 PASS。

完整共同算术构造是当前 formal-source 里的实质性缺口；本次没有完成其证明，也没有建立原稿反例。原稿的 class3 风险须保持为未解决构造义务，不能从现有源码模型反证越级推出。

## 静态核验边界

已读取相关生产 node/transition/graph、table atom/lookup、实际 Mathlib measurability、DCT、indicator integral、integrability 和 absolute-value API 源码。DCT 源 SHA256 为 `18b709ea5c9ef9136e3e75ded82a6135641e6e19688e0ca3abcb0af45648ab84`；Bochner/Set 为 `119710a23a0a09d22f770ca36844ddc3ca1d72cb479e231fe9ec06cea20629f9`；orientation 核对源 Unbundled/Abs 为 `7991bf23c32cc89e3a8f5cf0f054ddf49e84aa8326cbf5609e4addd70d8091da`。未执行其中任何证明。

八份 O/P Lean 的文本扫描未见 `axiom`、`sorry`、`admit`、`native_decide`、`run_tac`、`unsafe` 或 `#eval`。此扫描不是 elaboration 保证。两个新 project imports 仍映射到 source-only O 文件，依赖 M/O 的预期生产路径闭包未由本任务安装或编译。最终判定仍为：**局部 P10/P11 PASS；原始 H430 全链 HOLD。**
