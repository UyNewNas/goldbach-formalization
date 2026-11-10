# T07 · 原 36 项 W2 上表双素数反馈

43 个 Lean 文件供安装为 `ImbalancedChen/<原文件名>`。完整 SHA-256、Git blob、声明行、直接导入及公开原件在 [REGISTRY.json](REGISTRY.json)。按文件名排序后，逐行写入 `文件名 空格 小写SHA256 LF` 得到的总 SHA-256 为 `e7b60d88216e4a5c2de2883fb16573caac65c36604467ee738ac59da055ffa1a`。本包独立于原 T07 七源及 T01v3 七项表达修复。

**主要终端**是 `Part5OriginalH430W2UpperBankPayment.uniform_corrected_bank_base_only`（第 273 行）。它把修订五中
`occurrenceScale * (baseValue a + (bankPairArchive g a - bankPairIntegral g a))`
改进为原 `occurrenceScale * baseValue a` 的单侧上界。左边仍是实际 bank source gap、每项自己选中层的 Θ 修正以及所有原 Q80 舍入损失之和。右边保留一次 `ε * actualBankTheta`。阈值在 N、网格 n、根 k、τ、p、430 个前代索引之前选取。

## 文稿、脊线及原档

英文发布稿 `en/sieve-appendix.tex` 598–660 行给出原四个良好域、两种实际截点和总第五系数。Γ5 的完整计数先分为好坏两部分。Γ5 的坏部及完整计数的相应正代价留在原 base。Γ2、Γ3、Γ4 分别读小写 h 的三个原顶点 b、a₂、a₃，沿用冻结的 `Part5OriginalH430W2ArchivedSingletons`。英文 `en/numerical-appendix.tex` 说明 430 次递推只读前代，上表落到原 U3、U4 的指定位置。旧工作稿 `finite-w2-action-bank.tex` 的 pair-feedback 段给出 1024 格，下一个 `expanded-w2-midpoint-bank-and-table.tex` 的 outward-quadrature 段分别规定普通 base 256 格、双素数每片 64 格。

原三项的 `certify_finite_w2_action_bank.py` 和观测 JSON、其后 33 项的 `certify_expanded_w2_midpoint_bank.py` 和 `expanded-w2-midpoint-bank33-v1.json` 都来自 `tmp/publication-20261010/verification-renewal-v2/_runs/full-final`。公开发布的紧凑输入分别是 `finite-data/certificate-inputs/record-0026.json` 与 `record-0451.json`。144 组中全部有序 `(cellIndex,lowerQ80)` 文本在作者输入、发布输入与本次 Lean 字面量之间一致。其序列 SHA-256 为 `00f4cd9fe62bb8335fd07099bd3b9ca1c2a371a099c63b31642131749190d342`。另以 `original_lists` 对接原 `P2Selected430LiteralActionData.rows` 的完整 upperWeights 列表。

公开版本的 `certificate-map.json` 在 T4 明列两套独立复核。三行的 `record-0596.json` 记载 2400 个多边形查询、628 个正权重，并逐个检验上下端点。早期 `expanded33-w2-midpoint-independent-review.json` 曾把新增权重的数值重算列为待办。后出的 `record-0453.json` 明确记载所有 5224 个权重的上下端点均已另算。其 `record-0454.json` 保存逐 action、Γ、cell 的 112 位区间，`generator-0455.py` 用显式四阶导数及带符号 Simpson 余项，`record-0456.json` 保留几何复核。该外部档案与本包的 Lean 有理检查使用不同的重算方法。这里只读已有发布文件。

## 四个原域和导数

记 a₀=1/s₀，a₁=1/φ₁，a₂=1/φ₂，a₃=1/φ₃。全部 36 组五个参数都与 `originalW2At` 对应。对上表格 [a,c]，Γ5⁺、Γ6 的拉回是 (1-u-c/s₀≤v≤1-u-a/s₀)，Γ7、Γ8 的拉回是 (1-(1+c)u≤v≤1-(1+a)u)。原母区域如下。

| Γ | 原双素数几何 | 半开素数窗口上的截点 |
| --- | --- | --- |
| 5⁺ | a₀<u<v<a₂，v+2u<1；在 (1−a₂)/2 处分片，至 1/3 截止 | 固定 A=(Q/d)^(1/s₀) |
| 6 | (a₀,a₁) × (a₂,a₃) | 固定 A |
| 7 | a₀<u<v<a₁ | 母词 [0,0] 的第一素数 |
| 8 | (a₀,a₁) × (a₁,a₂) | 母词 [0,1] 的第一素数 |

`Polygons.clipped` 逐个取原域和两条 cell 线的全部仿射交点，严格位于母段内者加入端点表；排序去重后按中点取活跃上下线，保留正宽度片。端点证书给出 0<l≤r<1−u 及所有原域、cell 不等式。开放小条互不重叠且包含于严格原 atom。只需下界，因此可直接用非负核上的集合单调性；即使保留全部 knot 的潜在质量，方向仍成立。形状检查另核每条 Γ 的实存 piece 总数。

Fubini 和已有的 `P2EnhancedSeedPairD6Primitive.pair_inner_log_integral` 把每个原 `1/[uv(1-u-v)]` 小片精确化为
`f(u)=log(r(u)(1-u-l(u))/(l(u)(1-u-r(u))))/(u(1-u))`。
`Kernel.Op.jet` 在这个具体表达式上计算实际一、二阶导数，含乘积的 (2a'b')、倒数的 (2(a')²/a³-a''/a²) 和对数的 (a''/a-(a'/a)²)。`actual_jet` 同时证明所有光滑分母的导数及二阶连续性。原三行用每格非负 Darboux 下界；后 33 行取光滑 f 的中点和二阶导数的**有符号**区间下端 (m_2)，贡献 (h(f(mid)+m_2h²/24))。零截断在每条已积分光滑片完成后进行。引用 T01v3 精确版本 `P5OriginalSignedMidpoint.midpoint_bounds`。外部权重仍除 2⁸⁰，本包内部以 112 位向外舍入并使用 32 项有理奇次对数级数及其已证明余项。逐项回归到原权重的方向由 144 项闭合有理判定承担。

## 终端、重复与同 Q

- 第 103 行 `all36_four_original_pair_measures` 将每行每 Γ 在每个内部格的全部原权重除以 2⁸⁰，直接与该 Γ 的原 `pairIntegralAtom` 比较。第 178 行 `immutable_each_original_pair` 乘以指定前代的 `floorValue (precedingH g)`，保留 201 个端点的原 `floorKnotValue`。重复索引及同格跨 Γ 的重复出现都按原次数读入。上表守卫 [1,5] 和外部零值来自 `tableFunction false`。
- 第 202、222 行把同一比较送入原 `windowOccurrence N Q L d`。在 (Q=dN^L) 和实际素数平移下，前两个原窗口用固定截点，后两个是 [0,0]、[0,1] 母词窗口。原 `all_four_window_occurrences_reindex` 保留物理 PairGate、完整前缀及有序二元组。归一化权仍为 `localPrimeFactor d p · localPrimeFactor (d*p) q` 乘以原 `pairTest`。紧正的 L 区间给出一个阈值，先于 N、完整 d、Q、全部 j、k 和 430 个 g。此处由旧 H 乘的实际素数 profile 与原 sifted-count 状态仍是不同的数学量，后者的许可证保持待证。
- 第 243、259 行显式写出 `(∑ k : Fin 4, pairOldIntegral (originalW2At j) k (precedingH g))/5`。其被积函数是实际 (H_g(ρ_i(u,v))/[uv(1-u-v)])。归档表和质量各自保留一个 2⁸⁰ 缩放，四个双素数项只受一次原第五系数。第 264 行给出 `bankPairArchive - bankPairIntegral ≤ 0`，第 273 行用正 `occurrenceScale` 把这个方向传到实际 106 项 bank。
- `uniform_corrected_bank_base_only` 的继承条件为 ε>0、0≤t≤1/12、1/(n+1)≤11/384、p 为 N-互素素数且实际根带成员及 g∈Fin 430。原 Γ5 拒绝部分、长母词的所有重复和 unit、碰撞与普通/正换位 base 的带符号责任均保留。增长阈值、Θ 为零的分支和真实 rounding-loss 都沿用前式。

## 源的边界和安装

本次补足的是原有 finite integral 数据至实际 kernel/几何的对应、有符号中点实例化、旧 H 的合成，以及原 archive 差项的单侧消去。两套公开独立数值档案均支持指定区间；截至冻结，尚无这 43 份新源码的 Lean 编译、144 个有理判定的真假与资源结果、传递公理或 kernel 结果。有限检查分为 36 个独立可构建 action 模块，各含四个逐 Γ 闭式证明。比对还包括旧列表、弃零分支、归档计数及真实底层积分。整份 H34 仍待原 J₀=1/50 的增强可采族及四轮种子、带符号普通/换位 base、200 闭格上的实际前代计数归纳、同一 N 和 ρ 的 430+11 共细分及 U3/U4 各选中根的最终归一化。公开权重档案的可靠性并不能支付这些算术命题。

先安装 registry 的外部原依赖、冻结的 T07 `W2ArchivedSingletons`、v3 的 `P2DirectedLogRounding` 与 `P5OriginalSignedMidpoint`，再依次安装 Kernel、Quadrature、Polygons、StripMass。ArchiveData 可独立安装。Weights 同时用到 StripMass 与 ArchiveData；36 个 Check 模块均只依赖 Weights。BankPayment 同时导入完整检查和 `P2OriginalW2CountTupleReindex`。本包未改 production、此前冻结的 T07 或 T01v3。T09 已收到以上固定源并排队独审。截至本文冻结，h34、P5.6 及主定理继续保持原状态。
