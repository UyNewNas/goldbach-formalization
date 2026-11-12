# P2.9 原 248 代档案与吴的两条函数不等式

本批六件 Lean 源码用于审查。两条完整历史 W1 结论见下表。全部 W1、W2 坐标已接到同一普通吴母盒上的真实函数估计。W2 的四个良对素数域另已接入 30m 档案自身的逐项舍入和实际旧表。最终 29 个 H247 比较和 17,572 个实际母族的计数许可仍待证明。

|历史对象|本批结论|代际或量词|
|---|---|---|
|W1 第 69 条，零起算，\((s,S)=(3,5)\)|完整带符号候选至多等于自己的旧 \(H(5)\) 项。实际 `sourceW1Apply` 的竞争最大值保持目标格已得上界。|第 0 代候选非正。第 1 代由第 0 代的短格支付。读取第 \(n+2\) 代时只需第 \(n+1\) 代的 29 个短格。适用 \(0<\delta\le1/10\)。|
|W1 第 10 条，\((5/2,16/5)\)|首轮正候选恰为整数 \(1161320826237498322233\)，每个原目标格均满足候选除以 \(2^{80}\) 后不超过 \(H_\delta\)。|读取第 0 代，\(0<\delta\le1/100\)。保留种子仍需独立许可。|
|所有 70 个 W1 坐标|在合法点 \(s'=\max(s,S/(S-2))\) 实例化吴第一函数式，用 \(H_\delta\) 反单调性转回 \(s\)。|66 个原点直接满足比值门，余四个保留真实反馈积分和 \(s'\) 处的切换成本。|
|所有 36 个 W2 坐标|原 3 条和新增 33 条均满足 `MotherPair.AnalyticParameters`。原生完整母盒、三个 \(J\) 与四个合法 pair 齐备。两项历史 \(H\) 按实际 \(4:1\) 替入。|一个 \(k+1,\delta,\epsilon,T\) 同时支付本代 W1、W2 的原生式。读取 \(n+2\) 代两旧点仅需第 \(n\) 代短格。|
|所有 36 条 W2 的四组普通 pair 权重|30m 的 144 个有序下权重表逐组接上对应积分系数和逐项整数除法。采用 `outputAt g true` 的 200 个开格及 201 个结点。|每个 \(g<248\) 均读取自己的真实前代表。一个阈值先于各代，\(Q=dN^L\)、两个 Euler 因子和两项插入门都进入四个原母窗。|

## 两个完整 W1 候选

第 69 条读到的子格右端均至少 \(10/3\)。吴原生的 \(h_\delta(u)\le A(u)-a(u)\) 与 \(h_\delta\) 反单调给出 \(h_\delta(u)\le4/15\)。原生 `lower_seed_four_fifths` 给 \(a(10/3)\ge4/5\)。原递推在 \(2\) 至 \(7/3\) 上的 \(\log(v-1)/v\) 至多 \(1/6\)，故 \(A(10/3)\le19/18\)。原始与保留基底都不超过 \(-Q_{80}/10\)，反馈权重总和不超过 \(3Q_{80}/8\)。这两个单行离散界的有限证明体尚待核验证。原生成器 55–65 行的 \(1/2\) 已含在权重中。每项带符号整数乘积的舍入满足 \(\lfloor xw/Q_{80}\rfloor Q_{80}\le xw\)，故反馈至多 \(Q_{80}/10\)，整行由自己的旧 \(H(5)\) 支付。

读取 \(g=n+2\) 时，\(h_g\) 获自 \(H_{n+1}\)，\(H_g(5)\) 获自 \(H_n\)。已审低端点定理把 29 格扩为整段，历史保留不减性将 \(n+1\) 代的许可降回 \(n\)。`complete_row_preserves_at` 的额外前提只约束同一格此前的竞争者，对应 `max(current,candidate)` 的第一项。初代所有高 \(H_0\) 读点和所有 \(h_0\) 都为零。第 10 条正基底低于 \(1/300\)，原吴的 \(H_\delta(5/2)>1/300\) 及反单调性支付其全部实际目标格。

## 两类参数与同一母盒

原稿 `paper/source/manuscript-body.tex` 第 790–865 行给出 \(A-H\)、\(a+h\)、同一总 \(Q\)、母参数 \(\alpha\) 的变化、三个 singleton 和四个 good pair。吴原生树为 `09b97db5764ade1246bfb77206baa1b124760958`。`FirstFunctionalGainLimits.lean` 第 74–81 行要求 \(2\le S-S/s\)。四个违反该门的参数为 \((12/5,16/5),(12/5,17/5),(5/2,16/5),(13/5,16/5)\)。夹持换元后端点为 \(\max(2,S-S/s)\) 和 \(S-1\)，核为 \(h_\delta(u)S/[u(S-u)]\)。历史下格在 2 左侧始终为零。要支付这四条的一般基底，还须同吴在夹持处的 `firstFunctionalGainPsi δ s' S` 比较。

旧 W2 第 0 条的五个坐标为 \((11/5,227/50,353/100,29/10,61/25)\)，等于吴的 `SecondFunctionalParameters.row1`。`SecondFunctionalCoupledFeedback.lean` 第 44–53、63–89 行给的成本是

\[
4A(S)+A(\kappa_1)+\mathrm{classical}(p)+
\frac{2}{1-2\delta}\big(\mathrm{omega3XIntegralEnvelope}(\kappa_3,\kappa_1)+\mathrm{jointSup}(p)\big).
\]

增益保留 \(4H_\delta(S)+H_\delta(\kappa_1)\)、\(J(\delta,s,S),J(\delta,\kappa_2,S),J(\delta,\kappa_3,S)\) 和四个带插入门的 pair 积分。每个 \(J\) 包含原 \(a+h_\delta\)。`native_limit_with_historical_points` 替换两项原整数读价，其余项仍用此式。任意固定 \(k,\delta,\epsilon\) 下，`common_native_source` 先于 \(N\) 取一个 \(T\ge4\)，在同一 `wuSourceBox (k+1) δ N i Δ V` 给出本代两类动作的母盒计数。物理 \(Q=N^{1/2-\delta}\)，载体为原 \(P(dN)\) 与 `convolutionWuWindows`。

## W2 的实际旧 pair 费用

`P2HistoricalW2ArchivedPairWindows` 从 T07 提取的 `all36_four_original_pair_measures` 没有代、owner 或 occurrence 参数。它比较一格的有序系数和原物理 pair 域在此格的积分。对 30m 的两个原 JSON，静态逐块对照第 5–8 项 `(index,lower)` 字面量，144 组均与 T07 的 `weights j k` 同序同值。其元组、次序与长度的 Lean 有限证明体尚待核验证。旧行在不同阶段的重价只改基底。

`floor_numerator` 对每个乘积使用有符号整数除法不等式，然后按原下标归并。重复下标保留出现次数。两个 \(Q_{80}\) 分别归一化旧表和质量，外层 \(1/5\) 留在候选计算处。200 个开格加 201 个结点还原 `pairOldIntegral` 的原闭格取值，内部结点取相邻最小值。30o 的 `all36_four_true_old_H_profiles` 允许逐代代入 `outputAt g true`。`historical_pair_windows` 的量词先取所有 248 代共用的 \(T\)，再为该行固定物理元组 \(j\)，之后才选 \(N,L,d,Q\)。在 \(L\) 的固定正紧区间内，这四项真实历史反馈各至多为物理带权旧 profile 加给定正误差。要进原吴 `density`，还须把历史闭格 profile 同原 \(H_\delta(\rho)\) 比较并完成实际域与变元对接。该结论未采用 H430 前代表、增强母族或其带符号基底。

## 整行进入原吴极限仍缺的项目

1. 历史 W1 基底由 \(A(s)-A(S)\)、普通下系数积分和 \(-K\overline I/8\) 构成。30m 的原、保留基底切换于读取代 56。一般行须在实际 \(s,S,\alpha,\delta\) 上支付基底及其旧 singleton。四个夹持例还需比较 \(s\) 和 \(s'\) 的成本。原来使用的母族条件在 `finite-step-typed-closure-audit.tex` 第 196–265 行和 `generalized-one-step-double-sieve.tex` 第 32–104 行。
2. W2 存储基底含三个普通 \(a\) 项、四个普通 pair 成本、坏 \(\Gamma_5\) 的普通部分加回一次及正乘积替换扣除一次、\(\Gamma_9\)–\(\Gamma_{21}\) 的切换成本，含第 20、21 项的单商面质量。旧行在读取代 56、120 重定价，均相对于原基底。新增 33 条在读取代 184 加入。整行仍缺对应 \(\delta\) 下的带符号总成本比较、三项实存 singleton 与原 \(J\) 的连接、旧 pair profile 至吴 \(H_\delta\) 的比较。`expanded-w2-midpoint-bank-and-table.tex` 第 41–60、75–86、118–154 行和 30m 的 `positiveCost,w2Recalibration,w2VariableUpdateOK` 可核对每一费用。三个 \(J\) 的普通 \(a\) 基底只能使用一次。
3. 四轮短种子 \(2327/100000\) 的适用族在 `second-seed-certified-finite-feedback.tex` 第 5–30、113–137 行及 `second-seed-stable-prefix-extension.tex` 第 30–66、186–256 行定义。增强情形须保留完整前缀及所选余平方门、稳定 ceiling 和实际 cutoff，有限正标记族先固定。经典情形使用低于 \(1/2\) 的带裕量总层级及完整模数余项。原吴 \(Q=N^{1/2-\delta}\) 的 sourcebox 语义下，该历史种子的数值比较仍待证明。原稿允许先固定层级缓冲再取极限，这一量词亦需对齐。

`IMPORTS.json` 按源字节展开六个选本，共定位 474 个既有项目模块、1,652 个原研究模块及 244 个外部安装边界。T07 的旧注册给出 v3 的 `P5OriginalSignedMidpoint`。两个历史导入在 `1196b197` 的 Git 树命中此前所锁的 blob。另有两个间接依赖只定位到已登记或哈希冻结的本地草案，分别为 `P2EnhancedW1OrderedPositiveTripleWord`（SHA256 `2acb72ee…`）与 `P2EnhancedW1IntegerPrimeGraphStep`（`9db8da9b…`）。编译安装时仍须提供其选定源码。一次只读对象存在性查询在已设 `GIT_NO_LAZY_FETCH=1` 的 promisor 镜像中触发失败的自动取对象，未取得数据。后续本地 Git 查询已明确禁用 HTTPS。

`REGISTRY.json` 锁定六个选用源文件、八个历史 JSON、稿源、程序文本及依赖。`review-r1` 的两件选版分别明确 `H,h` 和 `Table` 所属命名空间。本批只做源文本、字面数据与 Git 字节身份核对。没有执行 Lean、Lake、LSP、安装、staging、数值 guard、producer、证书或旧历史递推，也没有远端写入。源级审查和 kernel 验证分别记录。

