# P1 singleton：实际剩余两长行的同源有限字典

**状态：SOURCE ONLY；未 elaboration，未编译，未 kernel 验收，新增形式信用为零。**

本目录把已发布的 `P1OriginalSingletonRemainingTypeIGeometry` 接到原 generic
`same_rho_mode_eq_fibres`。新增证明的适用对象是实际非零有序 HB tuple，保留原
`remainingTypeIValue/sourceTest` predicate。它不要求聚合
`blockCoefficient ≠ 0`，也不从单个非零项反推 signed 聚合非零。

固定源码锚为 `f3084a33ca08daf305ddd7c6eb660a038794614a`。
[SOURCE_REVIEW.json](SOURCE_REVIEW.json) 记录完整来源、SHA、半开字节区间、声明与证明体指纹、
互补 provider postimage 及静态审查边界。原 canonical、原归档和 driver 均未改动。

## 本次完成的源码合同

`P1OriginalSingletonTwoLongDictionary.lean` 新增三个公开 theorem 和一个私有有限索引 lemma：

| 声明 | 已写出的证明 |
|---|---|
| `actual_tuple_to_rectangle` | 从原 `factorTuples` 成员和非零 `assignedWeight` 导出 block/factor 列表长度与两条 `ofFn` 回环、原完整整数 rectangle 成员、完整乘积及 signed `hbSlots = assignedWeight`。相同数值的不同 occurrence 不合并。 |
| `role_position_mem`（私有） | 把单母项 `rowRoles` 和 `blockVector` 的同一 `Fin` 位置送回原 `roles.zip blocks`。 |
| `actual_tuple_long_role` | 用原实际 tuple 的实数 Möbius cutoff 排除长位的 `.mobius`，得到原 `.one` 或 `.logarithm`。 |
| `eventually_actual_remaining_tuple_dictionary` | 从实际 chart 支撑、HB order、真实 tuple 和原非零 remaining selector 导出恰两条不同长位置、最多四条短位置，并对每个频率直接实例化原 same-rho 字典。 |

主定理的量词顺序是：固定 `kap0 < 1` 和 `0 < zeta ≤ 1/20000`，先取 eventual
physical `N`，随后才量化 `kap/B/K/cj/row/Q/rho`。五条数值门槛由已有
`eventually_original_singleton_numeric_reserves` 从实际 `originalChart ≠ 0` 导出。
`group_has_long` 给出至少一长；原 `owns_product_window` 与 `atMostTwoLong` 给出至多两长；
原 remaining selector 排除一长，故原位置集合恰为 `{i,k}` 且 `i ≠ k`。

两个位置先于 `xi` 选定。最终恒等式仍使用同一任意 `Q`、signed `rho`、物理 `N`、
共同 rough cutoff 和单母项 `rowRoles`，保留 `roughFibreCore` 中原
`residueKernel q N (m*u*v)` 及其 exact coprime mean。载体包括 unit block 的 `{1}`
和原右闭 dyadic 整数区间；没有增加完整乘积截断，也没有改成严格 `U < n` 的载体。

## 原字节共享 supplier 与唯一 owner

| 新 source-only owner | literal imports | 原声明 |
|---|---|---|
| `P1OriginalSingletonTwoLongFiniteGeometry` | `P5ActualHBMediumBranchPartition`、`Part3TwoLongActualHBShortMass` | `longPositions`、`long_length_sum`、`long_card_eq_length`、`short_card`、`group_has_long` |
| `P1OriginalSingletonSameRhoFibres` | `Part3TwoLongRetainedRowReindex` | `same_rho_mode_eq_fibres` |

六条声明保留原 namespace 和所有证明体字节。唯一可见性改动是删除
`group_has_long` 前的 `private `；`long_length_sum` 仍为 private。

原文件位于 `docs/source-only/20261121-resume/p4-two-long-actual-row/ImbalancedChen/`：

| 原 provider | SHA-256 | 提取区间 `[start,end)` |
|---|---|---|
| `P4BOriginalNoMediumPairRows.lean` | `e08915d8c52725b1195069a0822a6e95239d89daceebe4e33a288d9ca679627c` | `[7168,9391)`，五条有限几何声明 |
| `P4BOriginalTwoLongActualDictionary.lean` | `0a8f213e63afc934afd1afa4aa8eaeeb850d5298201ec3db2a4232623ff69b33` | `[1059,3410)`，generic same-rho 声明 |

`provider-postimages/` 保存两份将来迁移时使用的互补版本：各自在文件首部增加一条新
supplier import，并删除且仅删除上表区间。移除新增 import、插回原区间可以逐字重建
固定 Git preimage。P4 `actual_pair_mode` 的声明和证明完整保留；新 P1 consumer 不调用它。

联合使用旧 provider 时，必须走这里的互补 postimage，不能把尚未迁移的原 provider 与
新 supplier 同时作为 owner 导入。本目录没有安装该路由，也没有迁入 canonical。

## 稿件对应与后续边界

复用共享缓存的固定 1106
[coefficient appendix](https://github.com/UyNewNas/chen-imbalanced-semiprimes/blob/a988cba584d803ae2856a0de50efb582f4f3dd6a/paper/release-20261106/en/coefficient-appendix.tex)，
Git blob `10f3e2efb2074a9b97148a5151956e1d450be13f`，
SHA-256 `267af54481f344e806d4cb3ad602aa7f32020b930845e2aa152b7daaa2f9a440`。
507–548 行给出原 trim、chart、HB、实数 cutoff 与每组至多六个 occurrence；621–630 行给出
no-medium 的一长／两长及真实 long roles；550–565 行的 Fourier L1 义务仍须后续支付。

此次静态核对确认六条原正文一致、两份 provider 可逐字重建、原 `actual_pair_mode` 不变、
所迁声明在拟议路由中只有一个 owner，以及五个新 Lean 文件无
`axiom`、`sorry`、`admit`、`native_decide` 或 `unsafe`。这些检查不构成 Lean 验收。
独立审查者 `/root/p15_resume_remote_delta` 已按冻结 SHA 核对三份新源码、对应 core list API、
两个 rectangle 定义以及两份 postimage，未发现具体合同错误或明确 API 错位；同样未运行 Lean。
新证明中的列表索引 API、两个旧 rectangle 定义的 definitional equality 和
`Finset.card_eq_two` 的 elaboration 仍待实际编译核验。

当前 `P5ActualLowerNormalizedAtlasOccurrence`、`Part3TwoLongActualHBShortMass`、
`Part3TwoLongRetainedRowReindex` 的已定位源码仍在 source-only 路径；本记录只固定实际使用的
supplier，不宣称递归源码／对象闭包已经就绪，也没有重搜已登记的历史缺源。

后续仍需完整 `remainingTypeIAtlas` 的 closed-block Fourier 复原与有限求和装配，保留原
eta/psi、group logarithm 和 roughness；随后接 rough-to-Brun、各个 sharp interval 的 strip、
E1/E3/E4、短系数质量、原模数矩以及全部 Fourier／外层预算。本目录没有写目标估计假设，
也没有支付 signed medium M 或 P3 谱核义务。
