# pp_derivatives 第六批 F：真实独立 singleton supplier 与窄上墙

本批新增 3 个 Lean 源码，共 884 行、62 个声明；仅写本 F 子目录。原完整 `task_complete=false`、`goal_complete=false`，完整派发项 `batch_target_complete=false`、`batch_target_source_complete=false`、`source_complete=false`。已完成的具体源码链另记 `local_step_complete=true`。全批未编译，`formal_credit=0`，不是 kernel/主定理验收。

进场先重核最终 E 源码、REGISTRY、REPORT 与冻结 reviewer 记录；E 登记的 22 个 raw 依赖 SHA 全部一致。C 的 8 个、D 的 17 个已登记 raw 依赖也再次核对。保留最终 E manifest，不重写旧批。D 消费 root 已批准命名空间静态更正后的最终 `f40cd3b0…`，未动旧源。

## 真实 endpoint support 与 scope

`P5LicensedLogAtomFamilySupport.lean`（201 行）对生产真实 log-grid atom 定义字面 `EndpointLicence`：每个 lower endpoint 减同一个 smoothing collar 至少 aStar，所有 upper endpoint 加 collar 之和至多 1。由实际非零支撑推原 normalized-log bounds，再推出每个 prime coordinate 至少 N^aStar、完整乘积至多 N；有限整数/素数支撑与 smooth/mixedEuler 固定 rank 字段均针对同一个实际 profile。有限 checked bank 继续使用 E 的统一有序 Euler 常数。

该 endpoint 谓词不是已经证明的原独立 u caller 穷尽：`checkedEndpointKeys` 仍待原调用证明其真实 endpoint membership。rough residual-q rank、physical t4 和 AtomKey 都没有被宣称为全部独立 u ranklist。

## 原独立素数 rank1 与实际窄 collar

读生产 `SingletonPrimeProductTransportP5`、`CurrentChenOriginalLowerFiniteP5`、`ChenInitialPrimeSource` 和 `ActualLowerSmallRoughAttachment` 后，transfer_lambda 确认真正独立 u 是原 `chenPrimePrefix N` 的素数坐标，并独占 same-Q/same-rho 的 arithmetic receiver。本任务供应函数和分析字段，单向供该 receiver 消费；不反向 import 对方未来的 PP 或 reserve 结论。

`P5ActualSingletonPrimeTestFamily.lean`（259 行）构造实际 rank1 函数 eta(u/N^beta)*chi(u/N)，N<2 时为零。它全实光滑、取值 [0,1]、支撑 N^beta<u<2N，在 2N^beta<=u<=N 上严格等于 1。固定实际 etaLog/chiLog jets 与有限 word Leibniz 给出先于 beta、N、word、point 的自然常数，导出真实固定 rank Family 字段和整数 Licence。此源的 2N 上墙不能悄然当成原 cap=N 的完整光滑测试；该差项保留。

为真正压短上墙，另写 `P5ActualSingletonLogCollarFamily.lean`（424 行）。在 u>0 取

`eta(u/N^beta) * chiLog((log u - log N)/delta)`；

非正 u 及 N<2 取零。实际 lower eta floor 使非正轴附近局部恒零，故对数奇点不妨碍全实光滑。函数仍在 [0,1]，在原区间 [2N^beta,N] 上等于 1；实际支撑上界为 N*exp(delta*log2)。使用 pinned mathlib 原始 `ConvexOn` 定义与 root namespace 的 `convexOn_exp`，由 0 到 log2 的弦线证明 exp(delta*log2)<=1+delta。因此 0<delta<=1 时，u>=N(1+delta) 处函数严格为零，原 caller 可取上墙整数宽度 ceil(N*delta)。没有执行指数数值评估。

正乘法 chart 上两个因子恰为原 scalar log lift；上墙只是 chiLog 的仿射缩放。实际 affine iteratedDeriv 字典、固定 chiLog 常数与有限 word Leibniz 证明每阶有序 Euler 界 C_q*(delta^-1)^q，常数先于 beta、delta、N、全部有序 word 和 point。小 N 与非正点由真实局部零覆盖，不以预算为前提。

具体选 `logWidth B N=(log2/log(N+2))^B`，证明 N>=2 时 0<width<=1，且 width<=1/log(N+2)^B；实际 mixedEuler 界为 C_(B,q)*log(N+2)^(B*q)。自然常数也先于任意 HB occurrence count、owner map、U 和有序重复 occurrence word，owner 映射严格保留 word 长度，不增加 rank 因子。`logWidth_family_fields` 与 `singletonLicence` 导出实际函数的固定 rank 字段和整数许可。transfer_lambda 已取得冻结 SHA，正将这个真实窄墙接回原 singleton source 的 lower-trim 与 upper endpoint arithmetic payment；这些付款不在本文件假装已证。

## 尚未闭合

完整原独立 u present-rank/caller 列表及其真实 endpointmargin 归属仍缺，故本批原派发目标没有完成。rank1 不能覆盖其它原调用，也没有用零 padding 填不存在的 rank。

另核得原 `PerGroupIntegerHBAtlasPushforward.atlasEval` 每个 group 含 psi(n/R)/log(n)，而 C/E 已建的 raw `A*eta*psi` chart 本身没有原 group 倒数 log。pp_fourier 保留原 exact atlas 中该因子；全 rank 的真正 normalized Family `A/prod(log(group))`、零附近光滑切断、mixedEuler 及 exact source 身份仍待实现。这是形式化供应衔接缺项，本轮没有证明原稿有数学缺陷。内部 PP/P1/P2/K 和最终主定理仍开放。

## 冻结字节

- `P5LicensedLogAtomFamilySupport.lean`: `de475a996c83bc9068b678c15916e3bc65e1f532c33248cb5064a4e81a1ad948`
- `P5ActualSingletonPrimeTestFamily.lean`: `f1fecd77ade8e2716aee270e580fdb742e1da3d5a08285ba88b68cf8e71313d7`
- `P5ActualSingletonLogCollarFamily.lean`: `12097ef913d455367a1dc54aa12d125eab535a6425e95a92bd3b02cdae30518a`
- `REGISTRY.json`: `e94e434c1d1c0b104adf06da179d702df59ba57b4481f723d37843825e53c6b5`

精确安装/import map、C/D/E 冻结 manifest、真正前提和开放义务见 REGISTRY。未运行 Lean/lake/checker/额度查询/新子代理/Git，也未修改 production 或先前批次。这里只做源码阅读、静态论证和 raw SHA 登记。
