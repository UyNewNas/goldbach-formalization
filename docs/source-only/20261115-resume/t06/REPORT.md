# T06：原 P1.4 去重审计与 singleton 粗素数修正

状态：**SOURCE_ONLY / UNCOMPILED / ZERO KERNEL CREDIT**。P1.4、Y07、Y08 保持未闭。本轮没有改动主图树、原策略、原数值或已有源码。

## 结论与不重复范围

主图树 `1_+_1.748_lean_proofs/main.md:61–119` 的父项仍黄；但其中“实际 dynamic parent / common history / 原策略成员”在原 source/core 量词下已有真实供应，不应再包装一遍。

- `1c0d8d19` 的 `P1OriginalFinalEighthMemberSupply.supply_of_history` 和 `cofinal_history` 固定原 third owner、当前/先前根、实际 sixth parent、四个历史门及同一 canonical state。`P1OriginalFinalEighthWeightedFrontier.cofinal_original_carriers` 随后在原 `cap=N,z=N^(19/96)`、普通 `w=0` 与正预筛 `w=N^ω` 上，给出真实 `1/(p−1)`、删去 `p∣N` 后的全 87 项遗漏。整个 Source 另有成员 iff，不能把“trim 内保证准入”误读为“所有边界点必定准入”。
- 已读 `544e3b07a5572a2ae21bad180e48e1cdccd91c91` 的 `INPUT_BOUNDARY.md` 及 `a023ae055d3d90738f6965a2848266aa13089faf` 的 `HANDOFF.md/REPORT.md`。其中第五/第六单侧 stopped 账等旧待办已有 `5d1786aa`、`4733b07d` 后继，不能按旧清单重复做。
- `4733b07d` 已付真实 receiver 的低模数、中心与高处支撑比较，并明确保留 `comparisonMiddle`、`savingMiddle`；`2ba389da` 已接最终矩形的独立 singleton 平滑、碰撞及 HB 恒等式。`b34153af` 已付最终 singleton 的原 OneLong 分支，亦不重做。
- Stored 72 块/292633 行、typed 143 形状、Q80 与 floor 均未作为本轮证明输入；没有重算任何表。

原稿的共同祖先与八层成员段属于**已有源码实现**。singleton 原素数低于 chart cutoff 的修正属于**可补的遗漏**，本轮给出下述真供应。其余原 signed PP 属于**尚未实现的实质解析输入**，不是只需重命名的接口。

## 新源码：真实 singleton 的粗素数修正精确为零

文件 `P1OriginalSingletonRoughPrimeReserveZero.lean`，六个定理；安装名为 `ImbalancedChen.P1OriginalSingletonRoughPrimeReserveZero`。

被消去的是已有 `P1OriginalSingletonMiddleTensor.singletonAtlas` 中的 **原** `roughPrimeReserve`。独立测试源逐字使用 `actualLicence kappa B N`，其真实 prime cap 为 `2*N`；原 residue、physical target 仍为 `N`。没有替换为另一个 Family，没有把 HB 中的粗支撑删掉，也没有引入筛外算术过滤。

证明的具体内容如下。

1. 非零 `listExtension (actualLicence kappa B N)` 在原 `primeTuples (2*N) 1` 上推出 `N^(1−kappa)<p≤2N`。这是从实际 narrow profile 的定义与 `profile_support_short` 读出的结论。
2. 固定 `kappa<1`，取 `a=(1−kappa)/2>0`。`N≥2` 给出 `2N≤N²`，所以 `(2N)^a≤N^(1−kappa)<p`。这只把既有 cutoff supplier 的环境上界设为 `2N`；没有把源函数或目标改成 `2N`。
3. 从同一个非零 `originalChart` 提取原 dyadic psi 窗。已修订并发表的 `independent_test_chart_cutoff_eventual` 在 `2N` 上给出 `beforeHBCutoff K js<(2N)^a`，故该原素数严格大于 cutoff。
4. 原 `roughWord` 在该 prime word 上等于一，实际 correction 的每个求和项为零。inactive chart 按原零值处理，不给它制造尺度。全 chart 和精确为零，无需估计 chart 数量或 coefficient 绝对质量。

量词是先固定 `K≥1,kappa<1`，再给一个 `N0`，之后对每个 `N≥N0`、每个 collar order `B`、每个原 trim 指数 `kappa0`、每个原 chart 和任意原 `Q,rho` 成立。`Q,rho` 的普遍性只来自项中乘了精确零；没有声称任意这种系数都享有 PP。

最后的 `eventually_original_singletonAtlas_roughPrime_paid` 直接读取原 `Params`、`products P`、`free P` 和已存在的 `singletonAtlas`，只删除已证为零的 `roughPrimeReserve`。保留

`trimReserve + Σ (mediumAtlas + noMediumAtlas − properPowerReserve)`。

新阈值仅依赖原固定的 `K,kappa`，因此可与 `original_single_prime` 已有的 `N0` 取最大；`r,n,e,q,a,m,β,k`、实际 `Q,rho` 和原正误差预算不需重选，也不多付误差。这是一个确切子项供应，不是完整 singleton 分布估计。

## 最小真实未付的历史输入

对原 `P1Original87SharpMiddleReserve.savingMiddle`，令

`B_N = floor(N^(9/20))`，`S_N = full87PhysicalSupport r n e q om N cap w z`，

`Δρ_N(d) = full87PhysicalRhoChange r n e q om N cap w z L d`。

需要在**原共同历史 schedule 已冻结的同一参数**上，按原合法正预筛选择固定 `ω>0` 与原 `ell`，再取 `cap=N,w=N^ω,z=N^(19/96),L=N^ell`，证明对任意给定正 `u` 有

\[
\left|\sum_{\substack{d\in S_N\\ B_N<d<N^{599/1000}}}
\Delta\rho_N(d)\left(\pi(N;d,N)-\frac{\pi(N)}{\varphi(d)}\right)\right|
\le u H_N
\]

对所有充分大偶 `N` 成立。这里的 `Δρ` 是原实际六层前驱减八层更新的完整小筛乘粗筛系数；实际 owner occurrence、剩余 suffix、各叶符号及该符号选择的 `β±` 全部保留。原 `H_N=frozenHN=singularNormalization`，`π` 保留原端点。阈值可以依赖全部已固定政策参数，但必须先于目标 `N`。

这就是该历史链下一笔仍需支付的输入，不能用以下任一替代：最终矩形 `Params.rho` 的估计；support-only 的任意系数族；source/core 的非负漏词权；`actualParent≤comparison`；或 `d≥N^.599` 上的系数消失。当前没有证明历史 `Δρ` 与最终矩形系数相等，也没有证明中段按 owner 相消。此处没有给出原实例反例；判断是**精确未付输入**，不是“原命题为假”。

`comparisonMiddle` 是另一实际系数：原 `eventPolicy true` 减 `eventPolicy false`，以原 `pairActualHighQModuli` 取和。其同一中段也仍需独立估计。最终 singleton 的粗素数修正为零不会支付这两笔历史账。

## 原稿约束与剩余职责

冻结原稿 `9731290e8f53cffda44129906cde6a965eaa869b` 明确区分：原八层 ordinary density 差；全模数 signed prime-product discrepancy；两份独立 density/compiler allowance。`distribution-prime-product-completion-20261010.txt:23–70` 将 restricted medium、全盒固定三分组及原局部四条长度条件作为实质前提；`lichtman-current-upper-density-assembly-20261009.txt:299–335` 要求全部政策、粗秩、平滑与网格先固定再令 `N` 增大。本轮不把 `exists_original_reserves` 中低段算术的“对后取 w 一致”偷换为完整 PP 对任意 N-adaptive w 一致。

最终 singleton 的 medium、two-long、proper-power/trim 的实际接回，以及上述两种历史 middle 仍在各自责任链；已有 OneLong 结论照原范围复用。全部同源 elaboration、kernel replay、传递 axioms 仍需另行验收。没有新增 `hOwner`、desired estimate 结构字段、`axiom`、`sorry` 或 native decision 证明。

## 本轮检查与交接

完成的是本地原始字节阅读、既有发布登记对照、手工数学/类型接口检查和 SHA256 冻结。只读 Git `show` 用于两份指定旧 P1 对象；没有 Git/GH 写入或 artifact 下载。没有运行 Lean、Lake、LSP、项目 helper、guard、fixture 或 candidate。`rg` 只读取新文件的声明与禁用占位符文本。

本包新 Lean 尚未 elaboration；不能据其六个源码证明体声称 kernel 成功。父节点保黄。后继应先静态独审此精确零分支，再在被允许时将本包两项直接 import 按 `FREEZE.json` 的安装选择纳入同源远端检查。不要复算已付的 actual member、OneLong 或 Stored 表。
