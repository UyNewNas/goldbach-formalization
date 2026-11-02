# Q22 — original second/third buffered caps and admission walls

状态：**SOURCE ONLY / UNCOMPILED / KERNEL UNVERIFIED / ZERO FORMAL CREDIT。完整任务仍 OPEN。**

本次供应真实第二、第三 `v` cap 的同一 pre-N 有限缓冲表，以及这些 cap 近似造成的实际 ordinary admission 差的固定 proper affine-wall 覆盖。它不是 P 的 source-signature 重排，也不是 O/P 最终 parity compiler 全部 mixed/changed 集合的覆盖。完整 87-domain 共同政策、两笔完整 `<u`、最终同一 rho 的 K 密度和支持指数均不升级。

只写本 Q22 目录。未修改旧源码、原稿、main.md 或 Git；未运行 Lean/Lake、编译器、CI、proof guard、数值重放或子代。所有 tactic/proof bodies 尚未执行。

## 原稿、旧供应与去重

已先读 Q/BRIEF，P 的 `all22_common_history`、`actual_two_reserves` 的 REPORT/REGISTRY，以及独立 `reviews/t26_review_policy_reserve.md`。原稿 `../chen-imbalanced-semiprimes/paper/source/manuscript-body.tex:453–509` 与 BRIEF 的 SHA256 一致；同读 `modules/global-positive-upper-completion-20261010.txt:183–242`。

原文 185–188 保留实际 coarse buffered cap；198–216 要先付小末素数 tail、在本身前缀上冻结祖先，再选有限高阶 caps，保留 open inherit/equality，禁止删除 child-wall 的父投影。229–242 另要求冻结政策后的 `C_policy*tau*omega^(-5)`、统一 rough-rank/support 和 compiler 选择。这些要求没有因本任务的局部结果而撤销。

显式检索了 production、source-only 批次及隐藏 `.lake/proof-continuation/source-reviews/drafts`。实际阅读了隐藏 `20261028-Coefficient-Sol6-EighthMask-Phase3/P5OriginalAdoptedEighthPhysicalMasks.lean:91–116,189–198` 和 `20261028-Upper-Pointwise/01-pointwise-dedup-gap.txt`。前者的 `PhysicalRows` 仍把全历史/平方/实际父 cap 条件装为字段，后者明确禁止用另一个 arbitrary-policy majorant wrapper 代替原 full policy；本次未作此替代。

以下现成供应直接复用，没有重证或复制：

| 既有源码 | 本次使用 |
|---|---|
| `ImbalancedChen/VariableEnvelopeRegularity.lean`、`BufferedFirstCubeGeometry.lean` | `qVLo_le_v`、`rationalInterval_v_error`；原 `v` 在 mu 两侧及跨 mu 的有效区间下界。 |
| `ImbalancedChen/SelectedPrefixRationalMesh.lean`、`LogPrimeBoxMesh.lean`、`FinitePrimeGeometryCore.lean` | 原有理端点、唯一半开 owner、全-cell lookup、mesh step 收敛、真实 ancestor 坐标。 |
| `ImbalancedChen/P1ActualCoarseLevelCeiling.lean` | `exponentValues`、`exponent_mem_values`；真正 Theta fallback 与全部原存储 coarse caps 的有限字母表。 |
| `docs/source-only/20261102-resume-30k/fallback_payment/P5OriginalCommonThirdScreenedSource.lean` | 真实 `selectedThird`、`secondExponent`、`thirdExponent`、`originalSeed_supported_interval` 与原 guard/gate 关系。 |
| `docs/source-only/20261028-resume-30e/coefficient_physical/P5OriginalCommonRefinedPreservation.lean` | `old3_after_two`，将原历史 decision 绑定到同一个 `originalSeed`。 |
| `ImbalancedChen/P5PresievedRoughSlotAffineGates.lean` | `original_upper_prefix_iff_log`，包含真正 total-product 和全部 odd-cardinality cubic-prefix tests。 |
| P `P4AUpperTaggedMixedWallPayment.lean` 与 `P4AUpperTaggedContinuationAccounting.lean` | 读取并保留固定墙的 arithmetic/residual payment、same-rho accounting；新文件不复制局部 strip/mass/slope 证明。尚未把新 admission-wall 事件无证认作其全局 mixed 事件。 |

Q01 的复用清点也已读。Q07、Q08、Q21 的并行任务没有被当作已供应的最终接口，也没有导入未落盘的最终结果。

## 新文件一：真正有限、严格 buffered 的原 v-cap 候选

`P4AOriginalBufferedFallbackCaps.lean` 定义单一 mesh 参数 `m`，原范围 `[0,19/96)` 上的二维、三维有理矩形。第二表用 y 的两个端点；第三表用 y+z 的两个端点。所有 owners 都在 `Finset.univ`，没有筛去不利 owner、平手或跨 mu 的 cell。`lookup_mem_alphabet` 明确给出对所有 N/history 有效的有限值域。

记 `Delta = (19/96)/(m+1)`，原 `originalSeed` 为 a，正 buffer 为 b。真实有效 caps 是

```
L2 = max(a, qVLo(y-cell) - b),
L3 = max(a, qVLo((y+z)-cell) - b).
```

这里 a 是既有原第三祖先所存的 cap，既不是理想 `v(x)`，也不是辅助 support-cover level。`oldAlphabet` 直接引用 production 的 `exponentValues`。`effective_caps_finite` 将这两个 max 放入同一个 N 前固定的有限 alphabet。

在原 `selectedThird` 和对应原 guard 上，从既有 `originalSeed_supported_interval` 与原 `new_cap_gt_old` 推出 `a <= v(input)-2e`；因此只要 `b <= 2e`，就有

```
a <= L2 <= v(y)-b,       v(y)-L2 <= (3/2)*Delta+b,
a <= L3 <= v(y+z)-b,     v(y+z)-L3 <= 3*Delta+b.
```

`exists_one_preN_buffered_fallback` 固定原 `OriginalData d`、`e>0` 和任意 `eta>0` 后，实际选择一个**有理** `0<b<min(e,eta/4)`，再由原 mesh-step 收敛选一个 `Delta<eta/12` 的 m。然后结论同时适用于全部实数 N、全部真实 history 的上述原支域，且两项 exponent 损失均严格 `<eta`。这不是“每个 N 再选 m”，不是输入 cap-error premise，也不改变既有 e。

`secondCap_ancestor`、`thirdCap_ancestor` 与两个 `effective*_ancestor` 保留各自真正的第二/第三祖先；后代不会重选早先的 scalar cap。有限二维/三维表使用同一个 m；原旧 mesh/support 标记继续作为共同 refinement 的独立有限坐标保留。

`bufferedSecondPolicy`、`bufferedThirdPolicy` 是明确的新物理 ordinary-policy **候选**，选中分支直接测试 `N^L2`/`N^L3`，不是与有效 cap 无关的记录。其源码证明：

- 前两层仍逐字用 old3；第三 action 仅在 rank3 之后生效，保留第二阶段的 rank3 decision。
- unsupported、small-third 与 unselected histories 继续用 old3；原 firstStop 没有重建或删去。
- `N>=1` 时原 old3 已接受的每一个 decision 仍被候选接受，由真实 ordinary admission 单调性和 `a<=L2,L3` 得出；没有假设 signed coefficient 或 signed density 单调。
- 全部 even decisions 仍为 true。

这不是全87已 licensed 的政策。特别是新缓冲政策向 fourth/fifth/sixth/eighth 的传输、原所有 selected-complement/full-square 许可、旧 gains 的 signed 保持和高阶共同 margins 尚未供应。本文件没有把这些条件变成一个 `History`/`full87` 结构输入。

## 新文件二：实际 admission 差的固定 proper-wall catalogue

`P4AOriginalBufferedFallbackAdmissionWalls.lean` 对每个固定 `r>=3` 建立 `Gate r = Option(Fin r)`：`none` 是全乘积 row，`some i` 是原 cubic-prefix row。实际 admission 只需要 `Even i.val` 的行；catalogue 保留全部 i，只是一个有限超集，不漏原测试。

两种 selected input 分别是 `t1`（原 p2）和 `t1+t2`（原 p2*p3）。每个 gate g 产生原 v 的两条墙：

```
gate_g(t) - (1/2)*input(t) = 1/2,
gate_g(t) + (3/2)*input(t) = 57/64.
```

每一 action、每一固定 rank 共有 `2*(r+1)` 个带标签行，线性 forms/offsets **不依赖 N、m、b 或 fine atom count**。`wallRow_ne_zero` 用原第一坐标的单位向量证明全部 forms 非零：选中的 p2、p2*p3 不使用 p1，而 total/cube row 在 p1 的系数为1或3。因此没有把 identity/equality region 当成零测 proper wall，原 v 两 limb 平手也不删除。

`second_actual_admission_change_wall`、`third_actual_admission_change_wall` 把真正 `ordinaryRosserPrefixAdmissible` 从 ideal v 接受到 `N^L2/L3` 拒绝的事件，定位到**该 history 本身**的上述墙，宽度分别为 `(3/2)*Delta+b`、`3*Delta+b`。长度、positive entries、真实 reverse order 是有限 log 字典的条件；cap 下界和全部墙 properness是结论，覆盖和误差小性不是输入。

`second_policy_change_wall`、`third_policy_change_wall` 直接读取新 `bufferedSecondPolicy`/`bufferedThirdPolicy` 的 false decision。第三版本显式只在 rank3 之后调用。`frontier_second_admission_change_wall` 进一步从真实 target-deleted `roughPrimeUniverse` 的 frontier membership 产生长度、正性和排序，允许任意 terminal mass；没有假定该点通过 buffered admission。既有 arithmetic carrier、目标素数删除和 history 顺序未改。

本文件没有把 coarse cap approximation 的 `Delta` 冒称为后续 parity compiler 的 fine `tau`。它也没有声称每个 O/P `changedMass`/`crossingMass` 点都属于这些墙：guard/owner change、old higher actions、全87分支、fine endpoint rounding 和所有 rank 的合并是不同的剩余义务。

## 同一 rho 与 continuation correction 的准确边界

O/P 的已绑定对象仍为

```
P4ACommonPolicyTaggedCompiler.compiledRho d N cap w z tau L
```

其 raw parent 是原 `P5OriginalCommonRefinedConstructor.policy8`，其中 fallbackSeed 仍为 pointwise v。Q22 没有修改该函数或把新 bufferedThirdPolicy 无证代入原 fourth/fifth gains。新候选对应的 raw rho（若后续作该实例化）应是 `actualSmallRoughRho (bufferedThirdPolicy ... false)`；它与 O/P 最终 rho 是需比较的不同政策，**本次没有证明它们的密度相同或接近**。

同一候选的编译/密度仍须调用 P 的既有 `compiled_density_eq_full_plus_beta_and_changed_minus_correction`，其恒等式逐字保留 `-p4aActualPresieveCorrection`。对单个最终上界，可用既有 correction 非负丢弃这项；对 old-new saving，两个 correction 的差仍须保留。本次没有新建方便的 rho、另选 beta pair、把 correction 设零，或把一个 raw 密度界相减当 saving。

## 尚未供应与两笔 reserve

1. **统一 full policy：** 把本次 cap 候选接入原全部第四/第五/第六/87第八原域和实际祖先，给全体 selected/full squares、旧 signed gains 保持与合法 common history。P 的 source-signature partition 不能替代它；Q07/Q08/Q21 的最终供应也没有被假设。
2. **完整 mixed-wall cover：** 从 O/P 真正 `changed`/`crossing` 定义推出每个被求和 d 落在一个 N 前冻结的墙/tail catalogue；完整处理 guards、coarse owners、open inherit、structural identities 与 fine endpoints。新文件只完成 cap approximation 的 admission 子事件。
3. **rank/support：** 导出真正政策的统一 J0、short/inherit branches 和 same-cell support inflation `<1/1000`。本次墙 family 是逐固定 r，尚未证明全 ranks 可截断为一固定有限并。
4. **总算术误差及速率：** P 已有每固定 proper canonical wall 的真实 strip×完整 residual mass 与 same-rho beta slope。仍要把以上实际总覆盖映射到那些载体，再求和并证明阈值/常数对所有后来的 fine atoms 一致。本次没有推出 `C_policy*tau*omega^(-5)`；properness/零测与该量化估计不能互换。
5. **density reserve：** 原 third finite approximation 已使用 `u_d/4`；完整剩余 coarse/activation/tail/old-new/all22 误差要严格小于 `3u_d/4`。本次 exponent 误差 `<eta` 不是 normalized signed density 误差，也没有消费 catalog5 端点或把 full third tail 再替换一次。
6. **compiler reserve：** beta 精度可由旧供应预选不等于完整 compiler `<u_c`。真正总 changed mass、同一 epsilon/omega/J0/tau 的共同次序和支持尚缺；未再花一次 density 的 quarter。

两个 allowance 仍各为原稿的

```
145007961227048312210593427530128000784681 /
11807308407697609823574244952794825721118720000.
```

`E+2u<K` 没有在新 Lean 中重证，也没有用该标量差冒充两笔实际付款。`P1.4.history`、`P4A.4.actual_all22`、`P4A.5.hdensity`、`P4B.4.hUpper` 保持 OPEN。

## 困难分类与静态检查

- **(2) 本次补出的遗漏推导：** 从已有原 `qVLo`/mesh/oldSeed 生成单一 finite buffered v caps；原旧 decision 的保留；对实际所有 ordinary total/cube tests 的 cap-change 定位；实际 fixed-family properness；真实 frontier 的 charged-point specialization。
- **(1) 未编译的 Lean 表达/API：** 仅作 declaration/type/namespace 的源码核对；全部新文件仍待 elaboration/kernel。修正了祖先坐标 helper 的实际 namespace，直接复用既有 old exponent alphabet，且将物理 policy 分支改为直接测试有效 max cap，避免未证明 OR/max 连接。
- **(3) 仍须查证的全局数学供应：** 完整政策的因果共同 approximation、完整 mixed-wall/rank cover、所示 omega 量化率以及两笔总 reserve。源码不足以推出这些结论；本次没有反例足以认定原稿为假。它们也不是再加一个 `coverage` 或 `error<u` premise 可以解决的 API 问题。

独立 q30 已静态读取两份候选及其原 API，对上述窄数学对应报告无阻断，并要求保留 fixed-rank/admission-only 与全 compiler 之间的边界。最终 review 位于 Q 的 `reviews/`，不在本目录代写。静态意见不计编译或形式验收信用。

精确 SHA256、direct imports、intended install modules、所有声明、复用路径及 remaining premises 见 `REGISTRY.json`。没有 materialize/copy 旧 Lean；两份都是本范围的新 source deduction，旧批次字节未改。
