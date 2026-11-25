# Γ5 物理光滑 profile：全秩 Euler 预算候选

**状态：ACCEPTED — 精确源码已通过 normal、stock replay 与完整 owned-declaration audit。**

本目录是独立候选；未修改原仓库、旧 `rank-candidate` 或既有 core。本代理未调用云编译；
主线程已执行下述初始版本验证。
修复后源码 SHA256 为
`798c9417b87278c82f1f9b763bf800e6bf0ab32324fe7312a609522d6c24372b`。
云作业 `ad5af8b1475349e7a8aa48789e358aae` 的三项验证均已通过：

| 验证 | 结果 |
|---|---|
| Normal | PASS；5.451 秒；closure 12、reused 11、failures 0。 |
| Stock replay | PASS。 |
| Complete-owned audit | PASS；11 个 audited owned declarations。 |
| 整体作业 | exit code 0；13.596 秒。 |

源文件有 **9 个源码声明**，审计有 **11 个 owned declarations**；二者不是同一种计数。
主线程提供的精确作业结果已归档，完整成功收据由主线程纳入统一 evidence 合包。
源码开头历史性的 `SOURCE ONLY / UNCOMPILED` 注释按原字节保留，以维持接受版本的
精确哈希；当前验收状态以本节、`REGISTRY.json` 与该作业收据为准。本代理没有重复编译。

## 初始编译与纯风格修复

云作业 `efc2bd28238c45ec83d4f2f48512f482` 的完整 stdout 已由主线程提供并本地读取：
严格 linter 处停止，原始摘要记录 4.048 秒、11 个依赖复用；没有报告其他 elaboration
错误，尚未执行 owned audit。
唯一诊断为第 68 行 `by congr 1 <;> ring` 应使用 `by congr 1; ring`。

- 初始源码 SHA256：`1e69c07920b1411797fc553202bfad7ac18924aec9090a98bd0b33e328f70d01`。
- 修复后源码 SHA256：`798c9417b87278c82f1f9b763bf800e6bf0ab32324fe7312a609522d6c24372b`。
- 修改前已断言完整初始 SHA；修改后已断言唯一字节替换就是上述 tactic 分隔符。
  所有 statement、import 与选项均保持不变。
- 初始源码、单行 diff、早先转发的诊断片段和完整原始日志均保存在
  `evidence/efc2bd28238c45ec83d4f2f48512f482/`。完整日志文件为 `cloud-full-output.log`，
  SHA256 为 `eda8cdeff915126f786949894a04b5ad98d2b9b2e5b3dc6b02f19b3836c01158`。

这一纯风格修复后的精确源码已通过上节所列新作业；失败历史保留，不冒充成功收据。

## 要补的最小推导

已接受 `PhysicalExtension` 已经证明，物理 profile 非零时每个原槽满足
`b / 2 < x i`，且全部槽的乘积小于 `exp(width) * N`。已接受
`EulerWordBudget` 已经给出任意固定秩上界 `K` 下的统一混合 Euler 预算。
本候选只从前者推出一个固定支撑秩上界，并接到后者。

固定 `a > 0`，定义

\[
N_0(a)=\max\{e,2^{2/a}\},\qquad K(a)=\lfloor4/a\rfloor_{\mathbb N}.
\]

若 `N ≥ N0(a)`、`b ≥ N^a`、`0 < width ≤ 1`，则

\[
N^{a/2}\ge2,\quad N^{a/2}\le N^a/2\le b/2.
\]

在任意非零 profile 点，每个槽严格大于 `b/2`；因此若总槽数为
`d = k + 2 + r`，有

\[
N^{(a/2)d}\le\prod_i x_i<e^{\mathrm{width}}N\le N^2.
\]

于是 `d ≤ K(a)`。这个推导直接作用于所有实坐标，保留每个旧槽、两个新槽和所有尾槽。
坐标值重复时仍逐槽计数；不折叠旧前缀，不去除重数。

若 `d > K(a)`，原物理 profile 在整个实坐标空间恒为零。现成 `slotEquiv`
只是双射重编号，所以原 `finPhysicalProfile` 也是整个函数为零。对该函数等式使用原
`eulerOne` / `eulerWord`，任意长度和任意重复坐标的 Euler word 都恒为零。
低秩情形直接复用现成 `finPhysicalProfile_boundedRank_mixedEuler_budget`。

## 最终量词与结论边界

对每个固定 `a > 0` 和自然数 `m`，得到先于所有移动参数选择的 `N0` 和 `C ≥ 0`：

\[
\begin{aligned}
&N\ge N_0,\quad b\ge N^a,\quad 0<\mathrm{width}\le1,\\
&k,r\in\mathbb N,\quad q\le m,\quad |w|\le q,\quad
  v\in\mathbb R^{k+(2+r)}\\
&\Longrightarrow
\left|\operatorname{eulerWord}_w
  (\operatorname{finPhysicalProfile}(\log Q,N,\mathrm{width},b))(v)\right|
\le C(1+\mathrm{width}^{-1})^q.
\end{aligned}
\]

`logQ` 任意。`N0(a)` 与 `m` 无关；`C` 只由固定 `a,m` 和现成低秩预算选择。
为同时覆盖 `q ≤ m`，证明只对这些阶数的既有常数作有限求和。没有新增 rank、
实际源 product cap 或待证 Euler 预算作为前提。

这里的 `b ≥ N^a` 是所考察光滑 profile 的显式参数条件。候选没有证明真实 marked
history 的每个素数至少为某个实际 `b`，也没有证明 profile 在该实际源上等于一。
实际共同 cutoff、源 admission、Family 装配、collar 支付和 prime-product 估计仍是
各自独立的义务。这个结论只闭合物理光滑 profile 的分析全秩预算。

## 1106 手稿对应与不重复检查

固定手稿 commit：`a988cba584d803ae2856a0de50efb582f4f3dd6a`。

| 原文 | 本候选的对应内容 |
|---|---|
| `sieve-appendix.tex` 494–532 | 固定 marked family 的正指数下界先于移动尺度固定；本候选保留固定 `a > 0` 的量词顺序。 |
| `sieve-appendix.tex` 584–620 | 保留 Γ5 原定义与完整母域；坏片没有被改为 ordinary admitted child。候选不改变任何 gate。 |
| `sieve-appendix.tex` 1090–1101 | 固定有限查询后才令 `N` 增长；本候选不给出真实查询族的具体正指数供应。 |
| `coefficient-appendix.tex` 318–331 | smooth prime-product 接口使用固定最大槽数、共同正指数下界、完整 product cap 与混合 Euler 预算。本候选补上非零光滑支撑的槽数控制。 |
| `coefficient-appendix.tex` 506–552 | 保留 original smooth chart 与 complete product；本候选不引入额外算术滤波，也不重证已有微分估计。 |
| `argument.tex` 359–387 | 正乘积后果的 bounded-rank 条件与本候选的分析支撑秩含义一致；该后果本身不在本候选结论中。 |

这一步属于已给正 cutoff 与完整 product gate 的省略初等推导。没有发现需要新的稿外
分析输入。对当前仓库 `ImbalancedChen` 与已恢复 H430 源的静态检索，没有找到同一
physical support rank、高秩整函数零或 all-rank Euler 结论。现有
`P2MarkedSourceRankCore` 是自然数完整列表在实际 `product ≤ N` 下的通用计数引理；
本候选不重编或导入它，只证明实坐标光滑支撑的实际必要接线。

## 源码声明

所有公开声明位于 `ImbalancedChen.P2FiniteMarkedGamma5AllRankEulerBudget`。

| 声明 | 输出 |
|---|---|
| `scaleThreshold` | 显式 `N0(a)`。 |
| `scaleThreshold_bounds` | `1 < N` 与 `2 ≤ N^(a/2)`。 |
| `physicalProfile_nonzero_rank_le` | 非零原 profile 自动给 `k + 2 + r ≤ ⌊4/a⌋₊`。 |
| `physicalProfile_eq_zero_of_rank_gt` | 高秩原物理函数等于零函数。 |
| `finPhysicalProfile_eq_zero_of_rank_gt` | 双射重编号后的原函数等于零函数。 |
| `finPhysicalProfile_eulerWord_eq_zero_of_rank_gt` | 原 EulerWord 整函数等于零函数，无阶数限制。 |
| `finPhysicalProfile_allRank_mixedEuler_budget` | 使用显式阈值的全秩预算，单个常数覆盖每个 `q ≤ m`。 |
| `finPhysicalProfile_eventually_allRank_mixedEuler_budget` | 同一结论的 `∃ N0 C` 形式。 |

另有一个私有 `eulerWord_zero`，按原 list fold 对零函数作直接归纳。
共 **9 个源码声明**（8 公开、1 私有）；这不是 audited owned-declaration 数量。

## 静态验证

精确 mathlib commit：`e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`。
已从官方仓库固定 commit 逐项读取本候选使用的实幂、指数单调、有限乘积单调、自然数
floor 与零函数 Fréchet 导数 API；精确 Git blob 和关键签名见 `REGISTRY.json`。
两项接受端源码 SHA256 与原接口记录吻合。最初的静态检查后，主线程先获得严格 linter
失败，再对唯一风格修复后的源码完成三项验收。初次失败与成功作业分别绑定各自精确
源码；静态检查与失败记录均未冒充 kernel/replay/audit 成功。

`/root/p2_rank_review` 已只读审阅精确源码版本，未发现数学、量词、整函数为零或 namespace
问题。原 `eulerWord` 已核实定义为 `List.foldr eulerOne`，私有零函数归纳使用同一个
constructor equation。独立审阅本身不构成 Lean 验收；随后主线程已经对当前版本完成
normal、stock replay 与完整 owned audit。
