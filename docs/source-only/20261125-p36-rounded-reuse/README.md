# 原 U5 rounded 输出：复用旧证明与完整物理模数入口

**本包为源码准备，尚未集成或编译，不计入完整 P3.6 验收。** 主分支基点为 `45428d4ef7eac2f19dfd17a3d3a9a4d0903296ce`；旧实现按 `c6b89774822580c731a236ac66dcd7466ac8a0e6` 的固定 Git 对象读取，未修改 donor 工作树。稿件仍为 1106 版本 `3ffa2d159c9974e2ca6d5f930c0f2c16baa0135e`。

## 更广泛去重后的修正

此前 rounded-count 冻结包和独立报告只核对了指定 main/donor 的 canonical 入口。继续检查旧 transfer 源码后，定位到 `P2RoundedU6NativeJointLedger.rounded_quotient_sum_le_sifted`：它已经对任意外乘数 b 给出了实际 rounded quotient minorant。因此本包将 `rowEstimator_le_sifted` 的重复有限展开改成直接调用旧定理；U5 的定义、定理陈述、原 ordered pair selector 与 exact coprime mean 全部保留。原冻结包和原报告保留为历史记录，不能把其限定的去重结论扩展到旧 transfer 文件。

同时定位到旧 `P2RoundedCausalFibreLossAndLevel`。它已经证明 same-label raw witness、mixed-fibre loss、rank × mesh 模数膨胀及先于 N 的统一网格。这里复用这些证明，不再建立相同算法或重证这些结论。

## 精确复用与依赖拆分

`REUSE_PREPARATION.json` 保存每个旧 Git blob、源码 SHA、抽取 byte 区间、原声明块 SHA 与可逆恢复记录。

- `P2LowerFiniteCellRounding`、`P2LowerFiniteCellBetaCompiler`、`P2LowerCanonicalRetainedTrace` 按 p15 已有修复源码原字节选入。旧 batch65 / batch90 的正常编译、官方 leanchecker、源与对象快照及日志原字节保存在 `prior-stage-evidence/`。这些既有阶段只按其原范围保留，不冒充本次完整目标验收。
- `P2RoundedQuotientMinorant` 原字节抽取一个现有 quotient 定理，保留原 fully qualified name。
- `P2RoundedFibreCore` 抽取旧文件前十三个定义与定理，保留原 namespace。唯一表达适配为对八个代码中的保留字 `universe` 使用 `«universe»`；去除这项 quoting 后逐字还原原声明块。原声明尚未在本包中 elaborated，故不声称已对比一个旧的成功 elaborated type。
- 两个旧 full 模块准备为兼容入口：import 新 core 并去掉已移动的声明；其余原字节保留。用原抽取块可以精确恢复完整旧文件。它们不在本包目标的编译闭包内。
- `P3OriginalU5RoundedCountInsertion` 仅改变上述 row 证明的调用方式。其原互素分子、signed primitive discrepancy、signed centre correction 和 labels/multiplicity 均未改变。

这样既保留原声明的 API，也不为一个通用有限入口引入 U6/U10/U11 的整条 analytic ledger 依赖。该拆分不声称那条 ledger 已完成验收。

## 新增的实际 U5 供应

`P3OriginalU5RoundedModulusCap` 只新增 U5 实例所缺的两个连接定理及固定 rough-rank 定义。

`selected_U5_raw_level_and_rank` 从真实 `selectedPolicy R bank buffer false N t` 的 raw 支撑出发，调用已有 pair-policy/tree 对应和已严格编译、内核复核的原 U5 accepted-word 上界，得到完整外标 pair × rough word 的 `153/256` 上界。实际 rough cutoff `N^(attachmentNu * epsilon^2)` 再给出

\[
\omega_{\rm pf}(r)\le
\left\lceil\frac{153/256}{(34/125)\epsilon^2}\right\rceil.
\]

这一步使用原 U5 pair selector，没有以旧 U6/sixth selector 代替。rank 只数 rough prime factors，small beta divisor 始终单独保留。

`exists_uniform_rounded_U5_modulus_cap` 把这两个实际输入交给旧的 `exists_uniform_mesh_physical_level`。在 `0≤buffer≤1/1000`、`epsilon>0`、`attachmentNu * epsilon≤buffer` 下，它选择一个 `tau>0`，然后才量化 N、bank、pair 与 modulus。对 count 入口中的同一个 actual rounded rho，得到

\[
\rho^{\rm rounded}_{N,t}(k)\ne0
\quad\Longrightarrow\quad
(t_1t_2k)<N^{599/1000}.
\]

small beta 的完整支撑成本已包含；outward negative rounding 使用旧定理内部产生的同 fibre raw witness，没有假设 rounded word 本身属于 raw retained support。最终严格指数界由先取中间指数再调用旧 `≤` 界得到。

这仍只是完整 carrier 的 envelope。它不把 `.599` 当作辅助 factorization cover，不供应公共 physical Q、whole-word atom identity、完整 (F)、density loss smallness、family admission 或 PP。

## 依赖与验收边界

本包的源码预检为 count 入口 147 个项目模块、rounded modulus 入口 264 个项目模块；与现有目标合并后为 272 个项目模块。新增选择为七个准备模块及仓内已有 `UpperCoefficientPerturbation`，无缺失、无环、无新增外部 import。原 264 个 selected 源码逐个哈希保持不变。`DEPENDENCY_PREFLIGHT.json` 保存实际解析出的全图与精确选源；预检不构成 Lean 或缓存信用。

本包未修改原 P1 `3aaf…` 任务的源码、对象或审计输入，也没有重跑已完成的编译与 replay。后续执行应先核对旧 batch65/batch90 的真实缓存、工具链、依赖及完整 sidecars，再决定哪些对象可复用。新增或改变 defining-module 所属的 core/消费者仍需严格编译、官方 kernel replay、完整 defining-module inventory、完整类型和传递公理审计。

当前允许的传递公理仍仅为 `propext`、`Classical.choice`、`Quot.sound`。没有引入 `sorry`、`admit`、新 axiom、unsafe 证明捷径或最终 PP 前提。
