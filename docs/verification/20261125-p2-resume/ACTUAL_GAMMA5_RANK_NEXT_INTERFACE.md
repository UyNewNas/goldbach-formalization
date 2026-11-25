# Γ5 实际秩与共同 cutoff：下一接口证据

## 状态与结论

**这是接口证据与下一步精确合同，不是新增 Lean 证明，不增加任何 green／accepted 信用。**

核对基准为固定 1106 稿 commit
`a988cba584d803ae2856a0de50efb582f4f3dd6a`；形式化工作的已发布参照为
`e008ae002d4cec5f01b127a11dbb13016be38c97`。

对现有实际 U3/U4 history 源，已存源码给出了共同正指数

\[
a_\Gamma
 =\texttt{frozenLeafCutoffFloor}
 =\frac{11/384}{6\cdot101^{440}}
 =\frac{11}{2304\cdot101^{440}}>0.
\]

若把这些**已有真实源供应者资格化并完成短接线**，则可取固定的自然数秩界

\[
k_*^\Gamma=\lfloor a_\Gamma^{-1}\rfloor_{\mathbb N},
\qquad b(N)=N^{a_\Gamma}.
\]

这两个参数由原 history 的共同 cutoff 决定；不需要另选 `1/90`、`200`，也不需要
把秩结论作为新的 admission 假设。当前缺少的是**已有 history 源的可用验证收据／
完整来源绑定，以及粗糙性到全槽秩的实际源组合定理**。没有发现秩与 cutoff 这一步
的数学反例或必须新增的分析定理。

该具体指数的来源范围是现有 U3/U4 frozen-history 实现。不能未经其他根的实际
cutoff 对接，就把它声称为整本稿所有 generation-248／430 families 的统一已验收参数。
稿的一般有限族使用先于 N 固定的正根级下界，见下节。

## 固定稿件定位

以下链接均固定到上述 1106 commit；本轮重新读取了对应原文。

| 原文位置 | 对下一接口的约束 |
|---|---|
| [sieve-appendix.tex 584–620](https://github.com/UyNewNas/chen-imbalanced-semiprimes/blob/a988cba584d803ae2856a0de50efb582f4f3dd6a/paper/release-20261106/en/sieve-appendix.tex#L584-L620)，`sv:two-step-gates`、`sv:singleton-domains`、`sv:complete-fifth-region` | 第五母域为全部 `a₀<u<v<a₂`。坏片为 `v+2u≥1`，**包含等号**；普通反馈只用于好片，坏片支付正乘积成本。物理比较 cutoff 为 `N^(L a₀)`。 |
| [sieve-appendix.tex 633–660](https://github.com/UyNewNas/chen-imbalanced-semiprimes/blob/a988cba584d803ae2856a0de50efb582f4f3dd6a/paper/release-20261106/en/sieve-appendix.tex#L633-L660) | `R=Q/B`；Γ5 使用 `q₁<q₂` 和 `Q_(q₁q₂)(R^a₀;n)`。余商粗糙阈值仍为同一个 `R^a₀`，marked 权重保持原样。 |
| [sieve-appendix.tex 893–920](https://github.com/UyNewNas/chen-imbalanced-semiprimes/blob/a988cba584d803ae2856a0de50efb582f4f3dd6a/paper/release-20261106/en/sieve-appendix.tex#L893-L920)，`sv:finite-seed` | 固定有限族的四步 seed；坏片 Γ5⁻ 不作 signed ordinary child 的分布断言。 |
| [sieve-appendix.tex 1033–1059](https://github.com/UyNewNas/chen-imbalanced-semiprimes/blob/a988cba584d803ae2856a0de50efb582f4f3dd6a/paper/release-20261106/en/sieve-appendix.tex#L1033-L1059) | 各根与后代保留共同 Q、旧 squares 与 stable ceiling。U3/U4、U10/U11、L5/L6 的具体入口分别说明，不能仅凭其中一类的实现覆盖其他入口。 |
| [sieve-appendix.tex 1090–1101](https://github.com/UyNewNas/chen-imbalanced-semiprimes/blob/a988cba584d803ae2856a0de50efb582f4f3dd6a/paper/release-20261106/en/sieve-appendix.tex#L1090-L1101) | 转移深度至多 440 时，残余指数至少 `λ_*·101^(-440)>0`，新素数指数至少再除以 6。先固定有限查询集，然后才令 N 增大。 |
| [argument.tex 715–734](https://github.com/UyNewNas/chen-imbalanced-semiprimes/blob/a988cba584d803ae2856a0de50efb582f4f3dd6a/paper/release-20261106/en/argument.tex#L715-L734) | U3/U4 使用 generation 430，其余位置 generation 248；共同有限逼近与正 cutoff 是另一步要求，不由“有限深度”一句自动给出。 |
| [coefficient-appendix.tex 318–331](https://github.com/UyNewNas/chen-imbalanced-semiprimes/blob/a988cba584d803ae2856a0de50efb582f4f3dd6a/paper/release-20261106/en/coefficient-appendix.tex#L318-L331) | smooth prime-product 接口要求固定最大槽数、每个原素数至少 `c N^a_*`、总乘积 `O(N)`、混合 Euler 导数预算。 |
| [argument.tex 359–387](https://github.com/UyNewNas/chen-imbalanced-semiprimes/blob/a988cba584d803ae2856a0de50efb582f4f3dd6a/paper/release-20261106/en/argument.tex#L359-L387)，`prop:current-positive-product` | 正乘积后果使用有界秩和共同正 cutoff；这里的 positive-product 常数 K 与本备忘的自然数秩界 `k_*^Γ` 不是同一参数。 |

稿没有在这些段落给所有有限查询族指定一个通用数值秩 `200`。一般形式应由该已选
有限族的正下界给出 `a_*=(λ_*·101^(-440))/6`，再从源的乘积约束导出秩界。
现有 U3/U4 冻结实现把根级下界具体化为 `11/384`，而且已经支付了共同 Q 冻结的损失。

## 不混用深度、因子秩和声明数

- `430`／`248` 是缺陷数组的代数，`440` 是稿中有限转移预算；它们不等于一个完整
  prime-product atom 的素因子槽数。
- 一个 atom 的因子秩是 `旧槽数 k + 两个新槽 + 粗糙余商槽数 r`，即 `k+2+r`。
  余商的所有素因子，包括重复因子，都必须计入。即使有旧词增长上界，也不能漏掉尾部。
- 本轮两模块的 `25+19=44` 是 audited owned declarations 合计，**不是稿内查询深度
  或因子秩**。若其他局部构造另有 44 步预算，同样不能直接把它用作 `k_*^Γ`。
- 不能把 equality-inclusive 的 Γ5⁻ 坏片改成普通 admitted child 来获得秩或 cutoff；
  本备忘的推导不使用坏片的 ordinary-square admission。

## 现成供应者、精确 FQN 与已知验证状态

### 已接受的消费端

`ImbalancedChen.P2FiniteMarkedGamma5EulerWordBudget.finPhysicalProfile_boundedRank_mixedEuler_budget`
已由作业 `24e632b1c7794c4c8fede0d6fa606e78` 接受，源 SHA 为
`761063d2147c7de6dc02bf6f616d1c4cb7be6d6f8da26f86c5e41c74755782a5`。
该模块有 17 个源码声明、19 个 audited owned declarations。其常数在 K、m 固定后，
先于实际 k、r、logQ、N、b、width、word 和 point 选择。

`ImbalancedChen.P2FiniteMarkedGamma5PhysicalExtension` 中的
`physicalProfile_eq_original`、`physicalProfile_nonzero_lower`、
`physicalProfile_nonzero_product_lt`、`tsupport_physicalProfile_subset_box`、
`hasCompactSupport_physicalProfile` 已接受于
`f1c4e308531844908cd1875e245dcf69`。这些定理本身不提供实际 arithmetic-source 的秩界。

### 已有源码供给，不能计作已接受的实际 admission

所有项目路径均相对本仓库根目录。

| 精确 FQN／声明 | 源码路径与作用 | 本轮可确认的状态 |
|---|---|---|
| `ImbalancedChen.Part5OriginalH430FrozenRootRefinement.frozenResidualFloor`；`.frozenLeafCutoffFloor`；`.frozenLeafCutoffFloor_pos`；`.frozen430_leaf_cutoff_floor` | `docs/source-only/20261102-resume-30m/h430_common_approximation/Part5OriginalH430FrozenRootRefinement.lean`。定义原指数并由 depth≤440 的实际 `Member` 证明 leaf cutoff。 | 本轮没有取得该旧模块的 accepted/replay/owned 收据；不得由已接受 Γ5 分析 core 反推它已验证。常数确切 namespace 是 `FrozenRootRefinement`，不是猜测的 `FrozenIntegerSupport`。 |
| `ImbalancedChen.Part5OriginalH430HistoryQuotientCounts.history_integer_roughness` | `docs/source-only/20261110-yellow-closure-10t/t07_h34_actual_counts/Part5OriginalH430HistoryQuotientCounts.lean`。对真实 `o∈rootHistory` 给 `ChenPrimeRough z d`、`N^aΓ≤z`、每个 `d.primeFactors` 因子的下界，以及 `N^aΓ≤cutoff Q d (227/50)`。 | 现有 Γ5 manifest 有精确 source pin；已知 accepted inventory、247-owner census 及本轮验证记录中未找到它的收据。source-only，未确认 qualified/accepted。 |
| `ImbalancedChen.Part5OriginalH430SeedHistoryMass.scale_and_alpha` | `docs/source-only/20261110-yellow-closure-10t/t07_h34_actual_counts/successor_base_seed/Part5OriginalH430SeedHistoryMass.lean`。对真实 `LevelIndex` 给 `0<d`、`L≥frozenResidualFloor`、`Q=d·N^L`、`N^frozenResidualFloor≤Q/d` 和 `2≤trueAlpha`。 | 同上：有原源码 pin，未确认 accepted/replay/owned 收据。 |
| `ImbalancedChen.P2FiniteMarkedGamma5SeedPlateau.enhanced_position_source_one` | `docs/source-only/20261124-p2-gamma5-log-extension/ImbalancedChen/P2FiniteMarkedGamma5SeedPlateau.lean`。现成 .U4 caller 已把前两项真实供应接到 `badLabels`／`roughNumbers`；输出旧素因子下界、比较 cutoff 下界和原 log plateau=1。 | 原 source-only 候选；本轮分析 core 的验收不覆盖这条 arithmetic caller。 |
| `ImbalancedChen.P2FiniteMarkedGamma5LogExtension.sourcePair_mem`；`.canonicalTail_prime`；`.source_fullProduct`；`.actual_raw` | `docs/source-only/20261124-p2-gamma5-log-extension/ImbalancedChen/P2FiniteMarkedGamma5LogExtension.lean`。给原 pair 下界、完整重复因子尾、实际 product gate。 | 这些在旧重依赖 arithmetic 部分，不能与同 namespace 中已单独验收的 `profile`／`profile_tensor_budget` 混算。尚无本轮独立资格化收据。 |

上述当前源码 SHA256 分别为：

- FrozenRootRefinement：`d05ebfcc10e8dde12560e87d99a9c47082c69995184e4aa2689bbec9fd92f8f1`。
- HistoryQuotientCounts：`1357863c8038c3711adef0122c0e31297d8bd26bb7cb6c8ca9b355f17203ee45`。
- SeedHistoryMass：`c908e063d57798c55f2709151cd05aab170b69f095157f2248645fe89d3e3932`。
- Gamma5SeedPlateau：`bd8cd06d0993b9006a699161631afac713013d7db589c8f1c32ffed2b38aae10`。
- 当前 Gamma5LogExtension 重 owner：`e4b8e7b53f4f8b4b869b683b8444d3d42f5c7dd469a63e4c7f5e8d698db6bd03`。
  这是轻量 profile 提取后的当前 owner，不能用初始 whole-file SHA 代替。

`ImbalancedChen.Part5OriginalH430FrozenIntegerSupport` 在这些旧源中被导入／打开，但当前
checkout 的 active 路径和 source-only 精确文件名查询未找到它。部分 requested-history
owner 也未由本轮窄查解析；不能用猜测的同名文件、别的版本或新的 admission 假设补洞。
这是一项**来源解析／资格化边界**，不是已经证明某个数学供应者不存在。

## 下一条真实源合同与推导

为最小化范围，先沿现有 `Gamma5SeedPlateau` 的 `.U4` caller 对接。保留它已有的参数：

- `N≥2`；现有 Lean 参数 `t` 满足 `0≤t≤1/12`；mesh 满足 `1/(n+1)≤11/384`。
- `p∈originalBand N .U4`；实际位置 `l : LevelIndex N n .U4 t p dep`。
- `Q := rootQ N n .U4 t p`，`old := (levelOccurrence l).current.old`，
  `d := wordProduct l = old.prod`。
- `qs∈badLabels N Q d`；
  `m∈roughNumbers ((N:ℝ)/(d*qs.prod:ℕ)) (cutoff Q d (227/50))`。

**所需结论**是对这个实际 atom 的完整原槽列表

\[
\ell=\mathrm{old}\mathbin{++}\mathrm{qs}
             \mathbin{++}\mathrm{primeFactorsList}(m)
\]

同时导出：

\[
\begin{gathered}
\forall q\in\ell,\quad N^{a_\Gamma}\le q,\qquad
\ell.\mathrm{prod}=d\,\mathrm{qs.prod}\,m\le N,\\
\ell.\mathrm{length}=\mathrm{old.length}+2+
                         \mathrm{primeFactorsList}(m).\mathrm{length}
\le k_*^\Gamma.
\end{gathered}
\]

这里不能新增 `∀slot, N^a≤slot` 或 `rank≤K` 作为调用者假设；它们正是要从上述原源
成员关系导出的结论。证明路线如下。

1. `scale_and_alpha` 与实际 history membership 给 `d>0`、原残余尺度；
   `history_integer_roughness` 给旧素因子 floor 和 `N^aΓ≤cutoff Q d (227/50)`。
   将旧列表各槽送入该 prime-factor 结论时，旧槽素性应复用原 history coherence。
   现有 roughness 证明已经通过 `rootHistory_coherent` 的 `hc.letters` 使用了它；
   本轮未重建该 helper 的完整 owner／验证闭包，不把它另标为已验收 FQN。
2. `pair_data`／`sourcePair_mem` 由原 `badLabels` 成员关系给 pair 长度恰为 2，且两槽
   都至少为同一个 cutoff；不要求坏片成为 ordinary child。
3. `mem_roughNumbers` 给 `m>0`，并给 m 的每个素因子同一个下界。
   完整 `primeFactorsList` 保留重复因子；`m=1` 时 r=0，无需删掉 unit case。
4. `actual_raw` 的 product 分支已经把余商上界转成 `d*qs.prod*m≤N`；
   `source_fullProduct` 及 `parentProduct old := old.prod` 提供同一乘积字典。
5. 令 `h=ℓ.length`。所有槽的下界与乘积上界给
   `N^(aΓ*h)≤∏ℓ≤N`。因 `N≥2`，取对数并除以正的 `log N` 得
   `aΓ*h≤1`，于是 `h≤⌊aΓ⁻¹⌋ₙ`。这一步不需要 prime distribution、PP 或 VM。

由此令 `k=old.length`、`r=m.primeFactorsList.length`，即可把已接受定理中的
`k+2+r≤K` 实参替换为这个**导出结论**，取 `K=k_*^Γ`。
列表索引保留每个原 mark 的 old slots、两个新 slots 和所有 tail slots；不能因乘积相同
而合并标记或省去重数。

## 与已接受物理扩张的参数对接

对固定 `width>0`，取 `b(N)=N^aΓ`。上述源合同保证实际源上每槽都至少 b，因而可以
调用已接受的 `physicalProfile_eq_original`；结合原 log plateau 后得到同一源上的值 1。
旧槽的对数和与 `log(old.prod)` 的转换使用已接受物理 core 的 product-log 字典。

同一个物理函数在非零支撑上逐槽大于 `b/2`，闭支撑逐槽至少为 `b/2`，全乘积小于
`exp(width)*N`。因此目标 Family 几何参数可对应为
`aStar=aΓ`、`lower=1/2`、`upper=exp(width)`，无需替换原 cutoff 指数。
这不是声称 Family 已构造；N=0、1 的全域总化、实际源 licence、collar 和系数选择仍要
通过各自原接口完成。源秩界来自源的 `product≤N`，不是从所有任意秩的 smooth outer
profiles 自动获得的全局消失断言。

固定 width 后，已接受 Euler bound 的 `C*(1+width⁻¹)^m` 可吸收进自然正上界，
对应 Family 的对数指数 B=0。若 width 随 N 变动，则仍需它的实际 inverse-width
控制；本备忘不偷偷增加 `width≤1` 或假设该控制已经成立。

## 缺失项分类与下一步限制

| 分类 | 当前边界 |
|---|---|
| 表达／API 接线 | List 产品与 Fin 槽总数、重复 primeFactorsList、实数幂／对数单调性、自然数 floor。属于短原生代数和有限索引接口。 |
| 尚未组装的真实推导 | 从实际 old/pair/tail 成员关系同时得到共同 floor、完整乘积≤N、`k+2+r≤k_*^Γ`。本轮未找到这条实际 Γ5 总秩定理，不能用条件性包装替代。 |
| 旧供应者资格化 | 上表 history/scale/arithmetic 源尚无已确认收据；缺失 owner 的精确源码及选择必须先解析。轻量分析模块的 accepted 状态不覆盖它们。 |
| 范围边界 | U3/U4 的具体 frozen 常数尚未对接整个 generation-248 family。Γ5⁻ 的坏 square 仍是正成本，不能获得 ordinary-child admission。 |
| 更后续数学 | 同一 selected-source prime licence、collar 支付、同系数 PP/VM 应用、完整 Family 和完整 P2 仍未完成。 |

本轮没有发现秩／共同 cutoff 本身的实质数学缺口；也没有把未验证的原供应者视为
公理或新增前提。下一轮应先复用并资格化既有供应者，再写上述一个实际源组合定理，
不重证明现有 Euler calculus。此次未提交云端任务、未重跑审计、未新增或修改 Lean。
