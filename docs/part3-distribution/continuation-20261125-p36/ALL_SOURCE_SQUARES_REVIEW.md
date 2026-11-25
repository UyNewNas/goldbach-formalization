# 原 U5 全来源与 signed 全词平方：独立源码审查

日期：2026-11-25。审查基点：`e4ad395e4901628d85a27d17d0f87a16ea943433`。

**结论：未发现已确认的数学矛盾、以目标平方为入口的循环、遗漏的短词／继承／fresh 分支，或替换原 signed rho 的操作。两份候选在源码层补齐了指定 `selectedPolicy R bank buffer false N t` 的全来源平方供应。它们仍未经过 Lean 编译、kernel replay 或完整公理审计，不能记为形式验收，也不等于完整 (F) 或整个 P3.6 关闭。**

本审查没有修改候选、原 receiver、fresh-fifth 文件或主 manifest，没有运行 Lean，没有另写证明。两个 visibility patch 的 exact-byte preservation 与 `git apply --check` 已由 root 核对；本审查读取了被引用的原声明及其调用语义。

## 1. 冻结对象与入口量词

以下路径相对于 `docs/source-only/20261125-p36-all-source-squares/`。

| 对象 | SHA256 |
| --- | --- |
| `ImbalancedChen/P3OriginalU5AllSourceSquares.lean` | `08533e66a1407643170456b72b1d7aff945f2c57ad3f301c0b249492b66dd243` |
| `ImbalancedChen/P3OriginalU5AllSignedSquares.lean` | `40407b717cf912873229eb0c2cb15a6069a5ec9469f0e5b404887a69fff1c361` |

`actual_U5_all_source_integer_squares` 消费原 `pairSupport N`、原 rough universe 的实际 subword，以及字面 `pairPlan R bank (2*buffer) (rootSeed false buffer N t)` 的接受结果。`native_U5_nonzero_all_source_squares` 再从原非零 `rho` 内部提取同一个 `s`、`chosen`、`k=s*chosen.prod` 和该接受结果。公开入口没有假设平方列表、最后来源、任意 mask、row-to-trace cap 恒等式或 `FreshFifth`。

最终 `native_U5_nonzero_all_signed_squares` 额外要求原标量分配：`0≤buffer≤1/1000`、`0<epsilon<1/8`、`R.epsilon≤attachmentNu*epsilon^2`、`attachmentNu*epsilon≤buffer`。这些是精度和缓冲分配，不是所求支持结论。它们须由最终有限家族的参数选择统一供应；该定理没有自行构造覆盖原稿全部分支的 bank 或固定共同 Q。

## 2. 实际来源、incoming cap 与所有长度

原 `P2OriginalPairSourceReceiver.checkedChoice` 先使用实际选择结果，再以 `freshCheck` 比较 incoming parent cap；检查失败或没有选中行均为 `.inherit 2`。候选 `finite_lookups` 用 `prefix_vector_code` 和 `prefixCode_nested` 分别推导 rank 3/4/5 的实际 lookup，证明 code 中补齐的未使用槽不会改变早先行；它没有将所需 cap 身份写成前提。原 `step` 的 admission 仍读取旧 `H.cap`，然后记录新的 frozen cap。

| 实际完整 rank | 来源及平方供应 | 审查结果 |
| --- | --- | --- |
| 2，粗词为空 | 原 `fifth_buffered_root_squares`；原两外标均 selected | 两个 full square 得到供应；空 complement 正确，不被冒充任意后续 mask。 |
| 3，一个粗素数 | 原 root 首个 rough-head reserve 与实际 `q₀≤N^(417/5000)` | inherit 调用原 `appendOne_gates`；fresh 使用真实选中 rank-three 行的 whole-box checks。 |
| 4，两个粗素数 | 实际接受得到 `S₃+3x₄<C₃` | 先在旧 cap 得到当前 square，再由 checked fresh／inherit 得到 `C₃≤C₄`，保留 `S₄+2x₄<C₄`。 |
| 5，三个粗素数 | 上一项 reserve 与原 rough universe 的 `x₅≤x₄` | 得到 `S₄+2x₅<C₄`；未添加奇数阶 cube 准入测试。fresh 与 inherit 均处理。 |
| 大于 5 | 原 `actual_postfive_integer_gates` 与 `run_cap_after_five` | 使用同一个实际 H5、来源、slots 和接受尾词；保留 cap，任意后缀仅追加 unselected 素数。 |

长度 0/1/2 在入口的显式 list cases 中处理；长度至少 3 时，从完整接受结果恢复 H5 接受，再复用旧尾部归纳。短词使用的重复填充值只占未使用向量槽，实际 prefix 长度和 code 投影排除了它们。

## 3. Mask 没有被遗漏或偷换

`Origin.row` 保存真实 rank、code、`SelectedBranchData` 和实际前缀素数向量。`Provenance.fresh` 要求同一 `select=some branch`、针对实际 incoming cap 的 `freshCheck`、以及字面的 `.fresh` action；其 slots 使用该行的 `branch.form.supportMask`。`Origin.root` 则明确使用原两外标。

`provenance_mask` 只声称继承和 post-five 尾部保留最后来源的 selected-prime list。真实 fresh 可以改选一个新来源 mask；候选没有错误地把它认作 root 的两个 true tags，也没有用 Trace 的全 false 编码替代 SourceForm 的选中集合。`physical_slots_to_integer` 仍把 selected product 放在 complement squares 的初始乘子中，没有将其设成 1。

## 4. 完整 canonical word 与同一个 signed rho

signed 文件调用已存在的 `original_word_data` 供应原素性、顺序、small/rough 分离与坐标范围。用同一 `s/chosen` witness 和原 `rho_at_pair`，它由原非零 rho 推出该 pair 属于 `activePairs`；随后调用原 `actual_signed_small_extension`。旧接口依原粗系数符号选择 beta-minus／beta-plus，这里没有取绝对值、删负系数或另造系数。

令 `C` 为该实际 run 的最后 stored cap，`B=t.1*t.2`、`r=chosen.prod`、`L=smallLevel N epsilon`。候选从非空素数词的 full integer squares 推出 `Br<N^C`，再从原标量分配推出 `L≤N^buffer`，所以实际供应的是消费端要求的 **`(Br)L<N^(C+buffer)`**，不是仅对观测到的 `(Br)s` 的较弱估计。

`source_cover_identity` 精确给出：root 来源的 `C+buffer=rootLevel false N t-buffer`；fresh 来源的 `C+buffer=rowCap R code buffer branch`。两个 square 列表在同一 cover 下附着完整 `s.primeFactorsList.reverse`，mask 保持最后来源，并由原 canonical-word 定理得到完整词等于 `(fullModulus t k).primeFactorsList.reverse`。

`SignedSupply.same_rho` 保持的是固定原外标 `t` 的原 native rho 与同一 small/rough pair coefficient 的等式。它没有把跨外标的 pushed-forward `integerRho` 总和及其 whole-atom 三因子表示也一并证明；后者仍须消费既有 signed regroup／pushforward 接口。辅助 cover 没有改写 coefficient、density 或物理 common Q，也没有被换成 `.599`。

## 5. 与 1106 原稿的对应及真实剩余义务

独立读取的稿件固定于 `UyNewNas/chen-imbalanced-semiprimes@3ffa2d159c9974e2ca6d5f930c0f2c16baa0135e`：

- [coefficient-appendix.tex](https://github.com/UyNewNas/chen-imbalanced-semiprimes/blob/3ffa2d159c9974e2ca6d5f930c0f2c16baa0135e/paper/release-20261106/en/coefficient-appendix.tex)：`coef:full-squares`、`coef:selected-squares` 的两套逐前缀平方及 cube-to-next-square 推导，与本候选对应；同节明确区分 physical level 和 auxiliary cover。signed small-beta 段保留实际符号与唯一 small/rough 分解。“Three-factor representations” 还要求局部 rescaling、selected-subproduct 区间、严格 reserves 和在整个 atom 上固定的表示；这些不由两套平方自动推出。
- [sieve-appendix.tex](https://github.com/UyNewNas/chen-imbalanced-semiprimes/blob/3ffa2d159c9974e2ca6d5f930c0f2c16baa0135e/paper/release-20261106/en/sieve-appendix.tex)：`sv:lower-exit` 及 lower-sign attachment 与实际 lower even-exit 方向一致；不能把 upper 段的奇数 cube 时序机械套到这里。`sv:finite-feedback`／`sv:child-state` 保持原共同 Q、residual 与 prime ceiling；候选没有重置这些量。
- [argument.tex](https://github.com/UyNewNas/chen-imbalanced-semiprimes/blob/3ffa2d159c9974e2ca6d5f930c0f2c16baa0135e/paper/release-20261106/en/argument.tex)：`eq:current-PP` 要求 AP 项与精确互素均值使用同一 signed rho。这里供应该原系数的支持数据，没有宣称已经得到其算术小误差估计。

因此，旧 `SQUARE_LICENCE_REVIEW.md` 所指出的“短词／继承／fresh 全来源统一接线尚无候选”已被本次源码推进，不能继续无条件复述为尚未写出。仍然存在的实质后续义务是：完整原 bank／W adoption、同一实际家族的局部 (F) 准入、whole-atom 固定三因子与符号重数重建、以及其算术分布估计。原 `formRankEligible` 明确排除 fresh `wSlot`；root 公式含 W 不等于已给出 W 的分解许可。既有 W／compact-upper 算法及 tensor 接口应复用，不能把源身份尚未接通说成这些证明不存在。

“all source”应始终解释为本定理字面 `selectedPolicy` 的全部实际历史；“complete signed squares”指完整 modulus word 的两套平方，不指完整 (F)。这是范围表达上的澄清，没有据此发现本候选的平方推导有数学错误。

## 6. 验收边界

两个 compatibility patches 尚未应用；六个被调用 helper 仍在主文件中为 private。后续集成须先按已冻结 patch 公开它们，并对改变后的依赖及两个新模块做相应 fresh 编译、bundled kernel replay 和完整声明／传递公理审计。源码扫描未发现 proof placeholders 或 `_private` 名字访问，不能据此替代这些验证。

本审查未重复上游 P3.5 whole-height 工作；按本轮已确认进度，其 81 声明已在 `5285d4f` 证据提交验收。那份既有信用与这两个仍未编译的候选严格分开。
