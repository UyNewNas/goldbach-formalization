# 原 87 域与真实物理余项独审

本次限定源码结论覆盖五个模块。原稿在 current-upper-density-assembly 第 343–433 行将原密度和编译储备分列，并在实际计数端要求同一 ρ 的带符号 PP。以下恒等和上界精确到两个仍需估计的算术对象。Y07、Y08 与 P1.4 仍为黄色。

## 三个不同的算术对象

- 历史 raw 与 licensed 的比较以同一个 (N,cap,w,z,L) 的实际两树在模数并集上作差。低段采用真实单素数 BV。上段使用旧 highq_same_supported_rho，在所有 d≥N^.599 令两个支持延拓系数相等。高处共同取何值未被确定。剩余 comparisonMiddle 用 Δρ(d) 乘含端点的 π(N;d,N)−π(N)/φ(d)，模数严格位于 floor(N^(9/20)) 与 N^.599 之间。
- 历史六层前驱与八层更新的差另取 full87PhysicalRhoChange。gain_eq_owned_sources 按 87 个 owner 的真实 occurrence 列表拆开。更新前从同一八层状态及其后缀使用 actualParent 的普通继续；更新后从该状态的 retainedOwner 读取 selectedCap，较晚的词仍读这位 owner 的 finiteCap。两边每个实际叶的粗积都严格小于 N^(299/500)。按该叶的真实符号取非零 β⁺ 或 β⁻，a<N^ℓ、ℓ≤1/1000 于是完整整数模数 a·leaf.selected.prod<N^.599。对上段模数的单点测试逐词为零，并集外依定义为零。得到的是实际增益系数的上段消零，剩余 savingMiddle 保留原符号。两个历史差均用原 FilteredSourceSupply 的已证存在顺序，每对树先各付 u/2 后再相减。
- 最终有限上区 bank、扩大第五库和 R17 层级使用独立的、带对齐宽度的矩形附着系数。其 c(d)≠0⇒d<N^.599 来自真实 joined 编译接口。单素数界直接对该 Q,c 重新应用；历史两树的条件没有被用来给最终系数发许可证。最终留有该 c 的 singleton middle，以及同一 c 在 switched 双素数整高秩区间的有限带实部。

## 完整模数、端点与费用

literal 在原 chenPrimeReceiverSource 的实际移位上求 d∣x 的和。交换有限求和得到逐 d 的真实 receiverTest。中心改换是精确的负号，原 π(N) 和 π(N;d,N) 都保留端点。对所有充分大偶 N、任意 squarefree、与 N 互素的完整 Q 及 |c|≤1，中心项的绝对值由 N−p 的实际互素约数预算支付，p∣N 时 p<N，且 frozenHN=singularNormalization。低模数 d≤floor(N^(9/20)) 的真 primeError 使用固定 A=3 的 prime BV。其精确互素均值改成 π(N)/φ(d) 需要原平方对数预算。BV、均值修正和中心各用 u/3；在低段取精确端点，在上段消去 d≥N^.599，未遗漏等号情形。泛系数的 eventual 阈值先于 Q 和 c，因而可交给任意实际同一系数。

原 87 行的 eighthSlots 是原数据 15–22 项的同一个 G87，已包含 winner9 两个同域加量。原 ordinary 增益给 (ΣI_j)−η<normalize(sixthRoot−eighthRaw)。正的 C_N/log N 将该式换回密度单位。在同一选参中，真实 compilerExpense 花 u_c，原预筛 correction 以负号保留，密度上界是 sixthRoot−G87·(C_N/log N)−corrEight+(η+u_c)·(C_N/log N)。这里给出了局部明确上界 U，整稿的最终绝对 K 仍须完成其余原账。对 w=0 与 w=N^ω 分别展示的 87 域漏量保持同一 ∏i(p_i−1)^−1·(1+profile) 和真实 owner 读取，所证为 missed·H_N<ηH_N。两种 cut 的不等式分别成立，数值密度用途仅减 G87 一次。漏量乘 H_N 的真实小量，与带符号的素数分布余项仍须区分。

给定 b、κ 和正 cap，先选同一 κ₀，再固定 K、η、ηSharp、ηCount。r,n 的门槛取最大，e 的范围取交集，随后确定 q,a、bank index m。FinePPSchedule 对该 bank、同一 r,n,e,q,a 选择一次 β 与 k，ω=νβ²、ℓ=νβ、L=N^ℓ，阈值 N0 覆盖选词、ordinary 增益、编译、BV 与 switched count。原物理密度、sharp 余项及 T05 的 band 使用的就是这个 Q,c。X_s≥0 许可把 X_s D 换成 X_s U。正计数仍保留 Re band(wholeHigh,c) 与 ηCount H_N；原傅里叶尾费只计一次。所述储备均无绝对 7/32 或任意对数消减的推论。

## 源与安装的界限

五个新源的 18 个不同外部直接 import、35 个关键旧源、6 个稿件对象、18 个已有登记及 9 个发表文件均按原始字节、SHA256/Git 身份复核。本包的 ORIGINAL_APIS.patch 按其指定提交对三处完整上下文逐 hunk 核验，每个变换只删除一个 private 和随后的空格（8 字节）。三个真实定理分别是 weighted_centre_fibre_sum、finite_coprime_fibre_bound 和 inherited_ordinary_leaf_admissible，全部原前提、返回值和证明体逐字保持。安装时须使用对应后像并重新绑定反向依赖，单列符号名不能据以使用旧对象。T05.PostModulusCount 的传递依赖须复用既有 ee04658e… 的 PostModulusRow 安装选择。已读原稿 9731290e 与物理源快照 3d15576a，所述缺口属于原稿货真价实的 distribution 付款。此次核查只进行源码、Git 对象与元数据的只读比对。


新增的 ORIGINAL_MU_SCOPE.patch 将原阈值 VariableEnvelope.mu = 25/128 显式引入六个实际祖先模块。四项从原发布 blob 出发；FrontierLeafCharge 和 FrontierInvoicesZero 先在内存逐 hunk 重建既有 FIXED599_API.patch 的后像，再核本次唯一新增行。六项分别复算 before/after SHA256、Git blob 并反向还原。新 OwnedGain 源的同一行移除后精确还原首稿 74d3dae3…。最终新源为 4def6a033e042a2526e1a6030697fd66b6adac4057d6ee8a1b7a8df6a5ac1d39。依赖变体须列入同源远端编译。

作者最终 REGISTRY 为 517d608f8868eb7c9eb33d3970ba50ee6c102c650b02ab05d3f8832dbe70a30d，REPORT 为 546b951404a826c2964c5ffd3eb0b0b734a86a6368408e0968b2c26f94aba33d。独审允许表 a19ce1c35665ea13cf3dab3a11035a2d4701b514d974151a9141cca7aaf9ccc1 逐件列出 9 个可发表文件，合计 135193 字节。此处无新的 kernel 或公理审计结果。

