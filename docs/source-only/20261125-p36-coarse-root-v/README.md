# 原 U5 root-V 的固定辅助 PairRange 几何

2026-11-25。**source-only；未编译；无 strict、kernel 或公理验收信用。** 本目录没有修改 main 源码、SOURCE_SELECTION 或验收队列，没有提交。这里冻结一个限定的小步：原 code 家族在 N 前固定的辅助 cover、V 路线与整 cell 余量，以及同一原 rho 的真实 root-source 平方支持消费端。

## 本候选实际供应什么

`ImbalancedChen/P3OriginalU5CoarseRootV.lean` 的几何输入只有原 `PairRange R`、正 buffer `b≤1/1000` 和辅助网格宽度。`exists_auxiliary_mesh` 直接消费旧 `tendsto_logPrimeMeshStep`，先取一个 `m_aux`，使

\[
\delta=(59/250-R.\epsilon)/(m_{\rm aux}+1)\le b/32.
\]

这个 `m_aux` 不取代原 `CandidateBank mesh` 的 `mesh`，也不传入原 pairPlan。新 native consumer 同时保留这两个不同的参数。

`family R m_aux` 是原 `Code m_aux` 的有限全集的 filter：保留那些 `codeAt R m_aux 2 [t,u]` 的几何 fibre 与原 U5 triangle 非空的 codes。其 predicate 不含 N、prime 或 native coefficient。`labelAt` 在 N 给出后才用 actual coordinates 读取已经固定的 label；它不按 N 新建 family。

`representative R j` 从这个纯几何非空 fibre 选择一次，因此只依赖固定 R、m_aux、j。它没有从某个 N 的实际 prime pair 选择代表。`closedCell` 直接取已有 `box R j.val` 的 first-two `qLo/qHi` 闭区间，并与原来的严格 U5 triangle 相交；不是另建 box 库，也不改变 triangle 的边界约定。`ownedCell_subset_closedCell` 和 `labelAt_closed` 将原 code 归属接到这个 hull。

`representativeRoute` 在代表点计算同一个

\[
\lambda_0(u,t)=\max\bigl(v(t),\max(v(t+u),B(a))\bigr),\qquad a=417/5000.
\]

它先检查 singleton 是否等于该最大值，再检查 pair，否则输出 W (`none`)。这些 equality ties 只决定**辅助**路线，不读取、更改或声称等于任何原 arithmetic policy 决策。它也没有假设 route 或 winner。旧 RootV 的逐词证明没有复制、泛化或重新安装到本候选的依赖链。

设代表点为 r_j，定义

\[
\ell_j=\lambda_0(r_j)+3\delta-b/2.
\]

复用旧全局 `v_abs_sub_le_of_le`，原 first-two hull 的两个坐标变化至多 δ，single / pair 输入分别变化至多 δ、2δ，常数 B(a) 不动。由此得到 `root_level_variation` 的 3δ 界，并由 `exists_fixed_auxiliary_geometry` 同时输出：

* `1/2 < ell_j < 153/256`；
* 对同一整个 cell 中每个 x，`lambda0(x)-b ≤ ell_j-b/2`；
* 如果代表点实际输出 singleton 或 pair，则这个**固定**前缀在整个 cell 上满足 `ell_j+b/4 ≤ v(prefixExponent(x))`；
* W 输出只保留代表点 `lambda0(r_j)=B(a)` 的身份，不供应 W factorization。

固定 V 路线在 cell 内其他点不必继续是其点态最大值；这里证明的是足以支付辅助 cover 的统一余量。该余量来自 `6δ≤3b/16≤b/4`，不是调用者给的 `hwin`、`hreserve` 或 `(F)`。

## 实际 rho / 原来源 / 原 mask 的接线

`native_U5_coarse_root_support` 的入口仍是

`rho N epsilon (selectedPolicy R bank buffer false N t) k ≠ 0`。

它先调用已有 `native_U5_nonzero_all_signed_squares`，原样返回 actual small witness s、原 rough sublist chosen、`k=s*chosen.prod`、实际 accepted=true、真实最后 source/slots 和 `SignedSupply`。新结论只在这个返回的真实 `source=.root` 分支适用。fresh-row witnesses 保留它们的原来源，未被改标。

`root_signed_auxiliary_support` 使用已有 `integer_gates_mono` 和上述 whole-cell cover，将同一 complete signed word 的平方从原 `rootLevel-b` 推到固定 `ell_j-b/2`。输出同时保留：

* 原 `fullModulus t k` 的 canonical prime-factor word 的 full squares；
* 原 source mask 在附着 small primes 后的 selected-complement squares；
* 原 `SignedSupply.same_rho`、`mask_preserved` 和 `canonical` 身份，均仍在返回 witness 内。

`root_signed_initial_complements` 再直接调用旧 `integerSquareGates_append_iff`，从同一完整词返回两个可能辅助 V 前缀的补集平方：singleton `t.2` 的补集是 `t.1 :: (chosen ++ smallWord)`；pair `t.2*t.1` 的补集是 `chosen ++ smallWord`。这只应用既有 append 字典，没有重做 prefix/tail induction、signed-small extension 或 greedy。原 S-mask 与辅助 V 前缀是两个分别保留的对象，不会互相替换。

native support consumer 本身对任意 `m_aux` 的共同 cover 单调性成立，因此没有额外 `hmesh` 前提；要同时取得增强范围和 V 余量，先用 N 前的 `exists_fixed_auxiliary_geometry` 选择同一 m_aux，再消费 native theorem。不存在把 N-dependent `levels N` 当作固定有限族的问题。

## 定点去重与唯一可见性补丁

本轮先核对了原 `LogPrimeBoxMesh`、`P2PhysicalIncomingPrefixCells`、`P2OriginalPairSourceReceiver` 及已有 `ActualExtendedThirdDyadicCoverage` / `ActualExtendedThirdGammaApproximation` / `ActualExtendedThirdWholeCellActions`。第三前缀的已有 diameter / representative-action 定理固定于另一套三维 dyadic label，不直接接原 PairRange 的 `Code m_aux`。本候选只补原 pair code 的必要连接。

| 本轮连接 | 直接复用的原声明 |
|---|---|
| N 前辅助 mesh | `tendsto_logPrimeMeshStep`、`logPrimeMeshStep_pos` |
| 原 half-open code 归属 | `exponentCode_membership`、`exponent_upper` |
| 原 qLo/qHi 宽度 | `qPoint_cast`、`logPrimeMeshPoint_succ` |
| 根 max 的 variation | `v_abs_sub_le_of_le`、Mathlib `abs_max_sub_max_le_max` |
| cover 的上下范围 | 原 `level_bounds`、`original_U5_level_le_cap` |
| 同 native rho 支持 | `native_U5_nonzero_all_signed_squares`、`integer_gates_mono` |
| singleton / pair 补集 | `integerSquareGates_append_iff` |

原 `qPoint_cast` 仍为 private。经主协调许可，本目录仅保存 `public-qpoint-cast.patch`：将这一个声明的 `private` 去掉，statement/body 原字节不动。绑定的 main `P2OriginalPairSourceReceiver.lean` SHA256 是 `8f01047a8664684a5388f068b8c170ec9ea0b052ed5b18ef2bb3c95155cd5da2`。`HELPER_VISIBILITY.json` 记录完整文件可逆重构、声明逐字保留和 `git apply --check` 的结果；补丁没有应用到 main，也没有使用任何 `_private` 名称。

`exponent_lower` 是原公开 `exponent_upper` 缺少的下端点方向；定点检索未发现已有同 statement。网格收敛、上端点归属、v 正则性、原 cap、all-source/signed-small/尾部证明都直接按原名调用。

## 本轮边界

这里的 ell 是**辅助 cover**。没有修改原 `rootLevel`、双缓冲 `rootSeed`、selectedPolicy、rho、density 或 physical common Q；`.599` carrier envelope 也没有出现在证明中。

本候选没有定义 fine endpoint vector、运行 frozen allocator，或证明 fixed-rank endpoint inflation 的 actual atom membership。后续 rough 部分可直接消费既有 `actualRoughPrimeVector_length_le`、`actualDwellSupport_upper_inflation` 与 endpoint-only allocation；其固定 J 只能用于 `[t.2,t.1]++chosen`。本轮传输的完整 signed canonical word 含 `s.primeFactorsList.reverse`，**没有**为它声称 N 无关的固定 J。

small beta 的第三组归属、exact signed tensor/scalar、monomial size 支付没有重做。W branch、fresh-row whole-box 分支、局部 scale family、physical common-Q admission、实际 row/F/bank 接线及 PP 估计也没有在此闭合。已有 whole-height 数学桥不列作本轮待重做项目。

## 固定手稿出处

唯一手稿 pin：`UyNewNas/chen-imbalanced-semiprimes@3ffa2d159c9974e2ca6d5f930c0f2c16baa0135e`。

* [paper/release-20261106/en/coefficient-appendix.tex](https://github.com/UyNewNas/chen-imbalanced-semiprimes/blob/3ffa2d159c9974e2ca6d5f930c0f2c16baa0135e/paper/release-20261106/en/coefficient-appendix.tex)，blob `10f3e2efb2074a9b97148a5151956e1d450be13f`：physical lambda 与 auxiliary ell 的区分、coarse A/W 与正余量、finite approximation 的 N 前固定及 ancestor-first 量词；whole-atom endpoint factorization 与 `coef:tensor-identity`、`coef:prime-product-insertion`。
* [paper/release-20261106/en/sieve-appendix.tex](https://github.com/UyNewNas/chen-imbalanced-semiprimes/blob/3ffa2d159c9974e2ca6d5f930c0f2c16baa0135e/paper/release-20261106/en/sieve-appendix.tex)，blob `bf8bae30ff18f21d716138af0cc6d9fbb4a80747`，`sv:finite-feedback`：physical common-Q 的 admitted marked family 及其 child laws。本候选不把辅助 ell 几何冒充这些 family 结论。

本轮是 [COARSE_ROOT_V_TRANSPORT_ANALYSIS.md](../../part3-distribution/continuation-20261125-p36/COARSE_ROOT_V_TRANSPORT_ANALYSIS.md) 中已审定的最窄辅助几何小步。constant-seed policy equality 仍只是一种可能的充分运输路线，不被声称是 common-Q 原量词的必要条件。
