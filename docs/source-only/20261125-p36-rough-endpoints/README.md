# Literal U5 的实际 rough rank 与 fine upper endpoints

2026-11-25。**source-only；未编译；没有 strict、kernel、类型或公理验收信用。** 本目录只保存独立候选及来源记录；没有改主源、SOURCE_SELECTION、编译队列或发布状态。

## 本次具体接线

候选 `ImbalancedChen/P3OriginalU5RoughEndpoints.lean` 直接处理

`word = t.2 :: t.1 :: chosen`。

其长度上界直接使用已有定义

\[
J(\epsilon)=\operatorname{actualRoughVectorRankBound}(\nu\epsilon^2)
=\left\lfloor\frac{5/8}{\nu\epsilon^2}\right\rfloor_{\mathbb N},
\qquad \nu=34/125.
\]

J 只依赖 epsilon，在 N 之前固定。native rho 的原 small witness s 仍单独返回，既没有展开 `s.primeFactorsList`，也没有把 small primes 计入 J。

`actual_trace_cap_le` 只实例化已有 `run_cap_le`：原 `pairPlan_fresh_cap_bound` 供应每步 cap ceiling，`original_root_seed_bounded` 供应字面的 `rootSeed false buffer N t` 上界。没有重新写 run induction。于是实际 `IntegerSupply.full` 的原 cap 不超过 `153/256 < 5/8`。

`integer_supply_endpoints` 从同一 `IntegerSupply` 使用 `integerSquareGates_at` 转换为旧 `actualDwellSupport`；原 `original_word_data` 供应每个原 rough slot 的 prime/positive 性、`smallCutoff=N^(nu*epsilon^2)` 下界和原 PairRange 坐标区间。随后直接调用旧 `actualRoughPrimeVector_length_le`。长度界没有增加 `hfull`、product cap 或 rank 上界作为新入口。

## 实际端点由原 cell 内部导出

端点分成两个定义：

* `upperByCode R m_fine N code = floor(N^(qHi R m_fine code))` 是固定 label 的端点表；
* `upperAt R m_fine N p` 用原 `exponentCode ... (coordinate N p)` 查这个表。

`m_fine` 与 cell-code 类型在 N 之前固定；端点的数值当然依赖 N。没有把依赖 N 的数值集合冒充固定指数 family。

`actual_endpoint_bounds` 使用冻结 coarse 候选的 `exponent_lower`、`code_width_le` 和原 `exponent_upper`。这些接口都显式接收 `m_fine`。令 `delta=meshStep R m_fine`，由真实 coordinate membership 推出

\[
p\le \operatorname{upperAt}(p)\le N^\delta p.
\]

左边由 `coordinate_power`、exponent_upper 和 `Nat.le_floor_iff` 得到；右边由 `qHi−qLo≤delta`、`qLo≤coordinate`、`Nat.floor_le` 及 `Real.rpow_add` 得到。调用者不提供 `hsize` 或一个任意 upper vector。

`exists_fine_mesh` 复用 coarse 的 `exists_auxiliary_mesh`，把其 buffer 参数取为 `8b/(J+1)`，直接得到

\[
\delta(J+1)\le b/4.
\]

这个选择只依赖 R、epsilon、b。原 bank mesh、coarse `m_aux` 和 fine `m_fine` 是三个独立参数；原 policy 没有被替换。

## 新输出与 native 身份

`RoughEndpointData` 的三个字段都是 `integer_supply_endpoints` 的输出：

1. 原 rough word 的长度不超过 J。
2. 每个实际 slot 的两边端点界。
3. 对整个实际上端点词，`actualDwellSupport (N^(storedCap + delta*(J+1)))`。

第三项直接调用已经完整证明的 `actualDwellSupport_upper_inflation`，没有重写逐点膨胀或 greedy。它对所有真实 source 成立，包括 short、inherited 和 fresh。

最终 `native_U5_rough_endpoints` 的入口仍是

`rho N epsilon (selectedPolicy R bank buffer false N t) k ≠ 0`。

它先调用已有 `native_U5_nonzero_all_source_squares`，原样保留同一 s、chosen、`k=s*chosen.prod`、accepted=true、实际 source、slots 和整个 `IntegerSupply`（包括原 selected mask 的平方与 provenance）。然后内部构造上述 endpoint data。既没有假设最终上端点支持，也没有改变原 rho。

只有这个实际返回的 `source=.root` 分支另外输出

\[
\operatorname{actualDwellSupport}\left(N^{\ell_j-b/4},
  \operatorname{map}(\operatorname{upperAt},[t.2,t.1]\mathbin{++}\mathrm{chosen})\right).
\]

证明使用原 cap identity `storedCap=rootLevel−2b`，以及旧 coarse 的 `rootLevel−b≤ell_j−b/2` 和上述 fine cost。输出到固定辅助 ell 时还剩 b/4；fresh-row source 没有被改标为 root。这里不要求 small-level allocation `nu*epsilon≤b`，因为整个小步只处理 rough word。

## 定点复用与依赖状态

本轮检索了现有 `actualRoughPrimeVector_length_le`／`actualDwellSupport_upper_inflation` 的实际调用点、原 U5 physical cap、all-source、FreshFifth 和冻结 coarse 源。现有消费者属于 generic／其他 third/pair 接口，未发现当前 literal U5 的同一 rough-rank＋原 cell floor-endpoint consumer。

| 本轮接线 | 复用来源 |
|---|---|
| 实际全 run cap | `P2ActualPairPlanRunSupport.run_cap_le`（保留原 `P2ActualPairPlanRawSupport` namespace）、`pairPlan_fresh_cap_bound`、`original_root_seed_bounded` |
| 原词 prime／rough 下界／坐标 | FreshFifth 的公开 `original_word_data` |
| indexed full squares | `integerSquareGates_at`、`actualNatList_cast_prod` |
| N 前固定 rank | `ActualRoughVectorEndpointBudget.actualRoughPrimeVector_length_le` |
| 原 cell 端点 | 原 `exponentCode/qHi/exponent_upper`；冻结 coarse 的 `exponent_lower/code_width_le` |
| N 前 fine mesh | 冻结 coarse 的 `exists_auxiliary_mesh` |
| 全词上端点平方 | `ActualRoughVectorEndpointBudget.actualDwellSupport_upper_inflation` |
| root 固定辅助 cover | 冻结 coarse 的 `whole_cell_cover/labelAt_closed` |

`P3OriginalU5CoarseRootV` 是明确的 source-only 依赖：本候选写作时它尚未安装在标准 `ImbalancedChen/` 路径。依赖的冻结源是 `docs/source-only/20261125-p36-coarse-root-v/ImbalancedChen/P3OriginalU5CoarseRootV.lean`，SHA256 `d6ad5b0c76fe2b87fd38058f31e4b903c2bf0ec04dd54b2e794f24e25ca060b7`，已在协调分支的文档提交 `93b715c2` 中保留。

原 coarse 要求的 qPoint_cast public-only 可见性改动已由主协调纳入 `0de9c51`；当前 `P2OriginalPairSourceReceiver.lean` SHA256 是 `18a9c43892b17b1961825b5a89e05e33e91448eb5ceb13eb4e73eba8277f5697`，qPoint 声明正文保持原字节。coarse 本身仍需主协调记录已从真实 P1 诊断识别的 `exponentCode_membership (m := m_aux)` 参数适配。新文件没有直接调用 `exponentCode_membership`；本轮也没有修改冻结 coarse 包或主源。后续安装、适配和编译由主协调单独处理，不能将这份依赖说明当成已编译成功。

冻结前再次逐项核对了公开接口的精确类型：`run_cap_le` 的 namespace 是 `P2ActualPairPlanRawSupport`，参数顺序为 `P, nu, hP, a, b, H, xs, hcap`；`integerSquareGates_at` 的入口为 `ps, hgates, i, hi`，B=1 后使用 `Nat.one_mul`；`actualNatList_cast_prod` 方向是“map 后实数积 = 自然数积的 cast”，与 `actualDwellSupport` 的前缀积目标相符。此处只记录静态接口核对，不记作 elaboration 验收。

## 范围与手稿出处

唯一手稿 pin：`UyNewNas/chen-imbalanced-semiprimes@3ffa2d159c9974e2ca6d5f930c0f2c16baa0135e`。

[paper/release-20261106/en/coefficient-appendix.tex](https://github.com/UyNewNas/chen-imbalanced-semiprimes/blob/3ffa2d159c9974e2ca6d5f930c0f2c16baa0135e/paper/release-20261106/en/coefficient-appendix.tex)，blob `10f3e2efb2074a9b97148a5151956e1d450be13f`：原 full-square `(S)` 支持、rough exponent 固定后的有限长度、whole-atom 上端点膨胀与 frozen allocation、physical lambda／auxiliary ell 区分，以及 `coef:tensor-identity`、`coef:prime-product-insertion` 的后续系数义务。

本候选供应 actual rough endpoint squares，没有构造整个 coefficient family 的 Cartesian atomization、运行新的 allocator、重做 small beta 卷积、证明 `(F)`、W／fresh-row whole-box licence、tensor identity 或 physical common-Q admission。finite rank 和端点支持本身不等于 well-factorability，也不闭合 P3.6 的 PP 估计。

constant-seed equality 与 direct admission 仍是先前记录的不同可能运输路线；本轮没有把任一充分条件误写成 common-Q 的必要条件。
