# 实际 U5 warm mixed fibre 的有限 proper wall 覆盖

状态：**SOURCE ONLY / UNCOMPILED / NO FORMAL ACCEPTANCE**。本包只新增本目录中的源码和记录；没有改 canonical、manifest、运行 Lean、提交或启动远程任务。它给出一条待编译的实际覆盖证明，不把覆盖当作输入，也不把它记为 mixedMass、density、PP 或完整 P3.6 的验收。

任务开始基点为 `4ee6c7c560a5c202ea73b28522d749faa6c303fb`。本包的真实依赖绑定在 rounded-reuse 已安装的 `88bad2514b057e323ed0adc00498f3af57820887`。旧证明一律从 P15 固定 Git 对象 `c6b89774822580c731a236ac66dcd7466ac8a0e6` 读取。精确 SHA、旧块起止字节和唯一命名空间均见 `SOURCE_INDEX.json`、`REUSED_SOURCE_INDEX.json`。

## 实际入口与量词

主文件是 `ImbalancedChen/P3OriginalU5WarmMixedWallCover.lean`。主要入口：

- `selected_U5_mixed_rank`：从实际 mixed fibre 中的原 raw witness，调用已有 `selected_U5_raw_level_and_rank`，再由完整标签相等把 rank 上界传到被计费的 `d`。
- `selected_U5_mixed_wall_cover`：在同一个实际 U5 selector、外部 pair 和原 root seed 下，给出 `d` 自身的 proper wall。
- `selected_U5_mixed_bounded_catalogue`：把前一条结论装入一个在 `N` 和 pair 之前就确定的有限地址类型。

入口保留 `PairRange R`、实际 `CandidateBank mesh`、`0 ≤ buffer ≤ 1/1000`、`epsilon > 0`、`N ≥ 2`、`t ∈ pairSupport N`、任意实际 enumeration cap、`tau > 0`、`d` 属于实际 rounded universe，以及该 `d` 的实际 `mixed` 条件。没有额外假设 d 被 raw policy 保留，没有假设 wall coverage、mixedMass 小、最终 density 或 PP。

记 `M = rawRank epsilon`，`r = d.primeFactorsList.length`，`xs = physicalWord N d.primeFactorsList`。结论给出 `r ≤ M` 和有限地址 `q`，其 rank 恰好为 `r`，满足

\[
L_q\ne0,\qquad
|L_q(\operatorname{wordPoint}(r,xs))-c_q(N,t)|
\le \max(1,\|L_q\|)\,\tau.
\]

`wordPoint` 只是 `xs` 的按原顺序的坐标函数；`ofFn_wordPoint` 证明取回整张列表恰好是 `xs`。它没有选择另一个保留代表。这里的向量只含 rough primes；原小 beta 因子没有放入 rough word，也没有被当成一个额外粗秩。

## 为什么覆盖的是 d 本身

旧 `mixed_pair_iff_canonical_warm` 给同标签的保留和拒绝两种完整 warm histories。新 `mixed_has_opposite_warm_word` 先检查 d 本身：若 d 保留，就选拒绝 witness；若 d 拒绝，就选保留 witness。随后的一切坐标距离、wall 不等式均以 d 的字坐标为左端点。

同标签的逐点距离没有重证 floor 算术：`same_floor_coordinate_le` 在两个单元素列表上调用已有 `same_floor_word_sum_le`，两个方向合成绝对值界；函数空间的 norm 界随后直接逐坐标得到。

覆盖有两个完整分支。

1. **粗码不同。** 某一个实际 exponentCode 不同。有限半开区间的归属发生变化，因此 d 自身的该坐标距离某个固定 mesh boundary 至多 tau。`none` 按原定义处理：不仅包括顶端，还包括所有位于实际 receiver 区间外的坐标。没有暗加“所有 rough coordinates 都落在 R.epsilon 与 ceiling 之间”的假设；实际 smallCutoff 可能比 R.epsilon 更小。
2. **粗码相同。** 外部 pair 的两坐标和 seed 在本次比较中相同。`physicalCode_eq_of_coarseWord`、`planChoice_eq_of_coarseWord` 和 `run_prefix_cap_eq_of_coarseWord` 逐前缀证明实际 lookup 相同、incoming cap 相同。`admissionView` 仅把现有 run/admission 读入旧的 generic first-disagreement API；`run_accepted_iff_view` 保留 incoming accepted flag 和全部祖先测试。由最终接受状态不同得到一个实际 admission 差异。长度为 2 的 pair root 排除冷根初始 square 分支；odd bypass 不会产生差异，所以发生差异的 full rank 必为偶数，恰好是原 cube。最后调用旧 `strict_row_disagreement_proper_wall`，得到 d 上的 proper wall。

这不是只测末端的新 policy，也没有重置 pair root。新 cap 仍在当前 admission 之后冻结。继承分支保持上一个 incoming cap；恒继承区域没有删除，也没有当作一条可丢弃的墙。空 rough word 不会产生分歧，已包含在旧 first-disagreement 的空列表分支里。

## 有限索引与移动中心

`P3OriginalU5WarmCapCodeStability` 使用实际 `CapPlan.choose` 的整个有限定义域：

```text
CapAddress depth mesh
  = Unit ⊕ (Fin (depth + 1) × (Fin depth → CellCode mesh × Bool))
```

`Unit` 地址给原 seed；其余地址给实际 `P.choose rank code` 在 seed 处的 freeze 值。fresh 地址保存真正的新 cap；inherit 只保留之前的 cap，归属由 run 的归纳证明传递。没有用任意外部 cap 表代替真实 plan。

在固定 rough rank r 上，`WallIndex depth mesh r` 是网格地址与 cap 地址的并：

```text
(Fin r × Fin (mesh + 2)) ⊕ (Fin r × CapAddress depth mesh)
```

`wallIndex_card` 给出其基数为 `r * (mesh + 2) + r * card(CapAddress depth mesh)`。最终 `BoundedWallIndex 5 mesh M` 对 `r : Fin (M + 1)` 作有限并。这个地址类型及所有线性行仅依赖粗 mesh、固定 depth 和 epsilon 的 rank bound；与 N、pair、bank 中实 cap 的数值无关。

具体行和中心如下。令 `S_ext = coordinate N t.2 + coordinate N t.1`。

| 地址 | 线性行 L 的向量表示 | 中心 c | 本包宽度 |
|---|---|---|---|
| `(i,j)` 网格地址 | `v_l = 1` 当且仅当 `l=i`，其余为 0 | `logPrimeMeshPoint R.epsilon ceiling mesh j` | `max 1 ‖L‖ * tau`，原点界实际为 tau |
| `(i,address)` cube 地址 | `v_l=1` 当 `l<i`；`v_i=3`；之后为 0 | `addressedCap pairPlan rootSeed address - S_ext` | `max 1 ‖L‖ * tau` |

cube 行是原字节复用的 `P5Z.PresievedRoughSlotAffineGates.cubeRow`。它虽作用在 d 的完整 rough vector 上，但只读取该 cube 的前缀。cap 中心可随 N 和 pair 变化。这里没有声称 literal rootSeed 已变成一张跨 N 固定的粗 cap 表，也没有改变原 rho。

## 旧证明复用与去重边界

`P3OriginalU5WarmMixedReusedCore` 保留原 namespace，精确抽取 12 个旧声明：两个 canonical-warm 入口，generic first-disagreement 的四个声明，strict affine-row crossing，以及原 prefix/cube/totalRow/cubeRow 的五个声明。旧块只发生一次已记录的 `universe` 保留字引用加引号适配；其余块逐字相同，包括原行尾。没有导入会重新定义 PlanCeiling 的重型旧 `P2ActualPairPlanRawSupport`。

固定 P15 的 `P4AFiniteCapTaggedConstructor/Payment` 也已窄范围核对：它们构造一个 clipped、tagged ordinary-upper policy，并把 historical Boolean/selector 放进 tag。该构造不是这里的实际 lower warm pairPlan，不能用其结论替换本包的实际 coarse-code/cap 绑定。这里没有重复其 upper-policy mass/payment。

源码 imports 预检：新目标闭包 **269** 个项目模块；相对 `88bad251` 的 **274** 个已选源码，并集 **279**；新增恰好本目录的 **5** 个模块，无 missing、cycle 或新增 external import。预检读取到后续 main `c5d32e919718a72880b17d9597cbedb592f2c0bf` 时，本目标闭包的旧依赖无字节漂移。根随后安装的 fixed-width 入口不在本包 import 图里；本记录不把该后续安装追记为旧预检。

完整旧 owner 模块不在本目标闭包中。未来若要同时加载它们，仍应将这 12 个声明的原 owner 改为兼容 re-export，不能让两份同名声明进入同一 import diamond。本包没有擅自修改那些 owner 文件。

## 给 canonical wall / weighted residual payer 的接线

本包到这里停止，不重写已有数论。下面是精确接口映射，尚不是本包已经证明的 payment theorem。

1. 置 `omega = attachmentNu * epsilon^2`，`v = 417/5000`。实际 rough universe 是旧 payer 的 `universe N enum (N^omega) (N^v)`。其量化质量供应需要 `0 < omega < v`；本覆盖只需要 epsilon 正，因此该小参数范围仍需在 payment consumer 中从所选 primitive 参数范围给出。
2. 对本包给出的 `r = d.primeFactorsList.length`，取旧 `canonicalPrefix r d`。旧 `canonical_prefix_tail_data` 保留真实 prime-box、单射、完整 residual divisor、coprimality 与乘积分解。旧公开 `P4AUpperTaggedFrozenAdmissionCatalogue.canonicalPrefix_ofFn` 可原字节复用，结合本包 `ofFn_wordPoint` 给出 `wordPoint r (physicalWord N d.primeFactorsList) = actualPrimeTupleLog N (canonicalPrefix r d)`。不要另写 canonical prefix/tail 算法。
3. 对每个固定 r，将 `WallIndex 5 mesh r` 中 `wallForm ≠ 0` 的地址取有限 subtype，再用 `Fintype.equivFin` 接成旧 `L : Fin k → (Fin r → ℝ) →L[ℝ] ℝ` 和中心列表。当前覆盖携带 properness，所以过滤不会丢点。`primeAffineWallStrip` 使用闭不等式，和本包的 `≤` 一致。
4. 新 `P3OriginalU5FixedWidthSlabReserve.exists_fixed_width_uniform_center_reserve` 适用于表中的显式向量。先对有限个 rank/row 选择宽度与共同 N0，再选一次 tau，使所有 `max 1 ‖L‖ * tau ≤ delta`。cap 地址和粗 rank 的个数均先于 N/pair，且 slab theorem 对所有实中心统一，所以不需对每个 pair 单独选 tau。rank 0 没有地址，也无需调用正维 slab theorem。
5. 将 mixed 的实际 d 装入上述 canonical wall union；对非负 reciprocal-totient 权重作有限并上界。直接调用旧 `canonical_wall_mass_le_strip_mul_full_residual` 或 `wallRoundingCharge_le_two_mass`，再用旧 full residual Euler-mass envelope。即使本包选择完整 rank，旧 canonicalWallModuli 是安全的更大集合；全 residual 质量仍由旧 theorem 支付，不能直接丢掉。
6. 最后调用原 `roundingLoss_le_two_mixedMass`，或使用旧逐墙 `wallRoundingCharge`；不要重复证明单位系数界或 beta normalization。beta 部分已有独立 rounded-beta 供应。density 接线必须继续使用同一实际 rounded 输出；raw-policy 的全称计数结论不能直接替代 rounded mean 或 P-dependent density。

## 开放边界及困难分类

- **形式化表达/验收：** 全部新源码尚未 Lean elaboration、strict compile、official checker、type/axiom inventory 验收。静态 import/hash/旧块检查不是数学验收。若后续出现 scope、List/Fin cast、definitional reduction 等诊断，应依真实日志修表达，不能提前宣称已通过。
- **有限接线仍待完成：** 上述 canonicalPrefix 坐标等式、proper finite subtype、uniform-centre slab 的有限并、完整 residual 质量与本 mixed 集合的有限求和接线。本包没有把这些待证结论作为入口假设；其几何覆盖已在候选证明中逐分支推导。
- **更高层实质义务仍开放：** 实际 rounded coefficient 的完整 density reserve、whole-atom/tensor/common-Q/admission/PP，以及 P3.6 总目标。这个有限覆盖本身不证明任何一项。

1106 原文定位：`coefficient-appendix.tex` 的 “Finite approximation and strict margins” 段要求保留 inherited 区域、先冻结 coarse decision 再 refine children；`sieve-appendix.tex` 的 `sv:physical-lower` 明确 physical lower density 还需要 absolute beta 与 box error，而不能只从 coefficientwise order 得出。两份稿的精确 Git blob 分别是 `10f3e2efb2074a9b97148a5151956e1d450be13f` 与 `bf8bae30ff18f21d716138af0cc6d9fbb4a80747`，索引同时保存 SHA256。
