# 旧种子两上锚、三个负窗与同 Q 的计数余数

独立源码审查通过限定端点 `Part5OriginalH430SeedAtSignedAP.initial_and_four_rounds_at_signed_AP`。七份新 Lean 源码、28 个公开声明、八个直接外部依赖与原 26 源前件的确切版本均已核对。七源码排序指纹 e0f2dfa2d5a6d927ec2c160935cee3df4238af58a45418b1c12446cde3a92f95；作者 REGISTRY 2fb25c5b990d7e56297fdedfb6d7deb89142abda4e46a7b7b2b3bb765c88d25d；作者 REPORT 503c12ddcbb5c4a44f53771171e4f94ca62b13fe53076fdb28db10168a8f48e2。独立读回登记中 49 个不同本地文件，并沿不可变提交树核过 45 个不同的提交/路径条目。八个外部依赖中的 PhiBounded 使用原生 09b97db5 树中的 blob 1832ba22105bf8bc80fef7846e2b9f6cab1ba3cc；P2SameQPhysicalRosserSeed 复用 a681ec71、cdc81d65 两树中相同的 4ff82f7f… 源码。其余六项为两份既存工程接口和四份旧 T07 文件，完整八项见白名单复用栏。

## 原母词与真实水平

`physical_main_sides` 对固定 κ, ε > 0 给一个 T ≥ 4，随后任意充分大偶数 N 和实际 d,Q,z,s 满足 0 < d ≤ N、Q/d > 1、z ≥ N^κ、s=log(Q/d)/log z ∈ [2,10]。用 dN ≤ z^(2/κ) 支付可移动模数的局部 Mertens 误差，采用原整水平 floor(Q/d)+1、li(N)/φ(d) 和 θ=4 li(N)C(dN)/(φ(d)log(Q/d))，给上、下 Rosser 主项的有向界。lowerBar 的符号处理复用现有双向局部乘积估计。

同一冻结根 Q 的正整数幂是 N 的整数幂。实际子素数 q∤N 时，若 Q/(dq) 为整数则 Q 是 q 的整数倍，与该恒等式矛盾。因此 ceil(Q/(dq))=floor(Q/(dq))+1。旧素数积严格筛 p<z 且 q≥z，子模数变为 dq 后积相同。φ(dq) 保留，允许 q 已出现于 d。真实对数坐标不会落在有理窗端点。三个原半开窗以 50/227 起，分别止于 5/11、10/29、25/61，子参数 (227/50)(1−u) 落在所需区间。单窗 θ 质量界 4θ 使 ε/8 的逐子误差至多支付 ε/2，余 ε/2 用于原窗的一素数主项。三窗再以 ε/3 聚合。两正锚点 s₀=227/50、φ₁=353/100 保持原 4、1 重数。窗和锚点付款对任意同层有限标记子集 B 有效。

## 精确终端与余数

固定 ε>0、J<actualJ2omega，先选 T，再取任意大偶数 N 和真实 n,k,t,p，其中 0≤t≤1/12、1/(n+1)≤11/384、p∈originalBand N k。最终定理采用 S=seedPositions N n k t p，D=S.image wordProduct 和 σ=groupedSigma S wordProduct levelMark。中间允许任意 B 的均值定理与最终指定的 S 分开使用。`true_seed_to_mother` 由前 60 格的实际正种子与接收者粗筛阈值包含得到单向母计数上界。重数由原 mark 和乘积纤维求和保留。

令 C=∑ₗ∈S mark(l) trueAt(l)，Θ=markedTheta S。E 是三个原真单素数母窗计数之和减去相同下 Rosser 多项式，经原 σ 求和。E≥0，回代原 21 项计数时位于左边。令 A 为两上锚按 4、1 加权的实际带符号 AP 余数，P 为原 π 居中的三负窗余数，G 为含四正双窗及切换正素数族的 signedPositive。则初始端点为 5(C−(1−1/50)Θ)+E ≤ A−P+G+εΘ。对每个 r∈Fin 4，原 J_{r+1} 取代 1/50 后，右边另有 5J_r ∑ₗ∈S mark(l) physicalFeedback(l)。physicalFeedback 原已含 1/5，且只含三单和四个好双窗；坏双窗没有前代反馈。原《second-seed-certified-finite-feedback》固定同一上一轮、迭代 4 次，上端点的真实计数/余差均按此顺序保留。

初始真计数改进尚须在许可的原标记族支付 A−P+G−E。四轮还须给上一轮真实 Buchstab 子计数和好双窗计数，控制加上七窗反馈后的总余数。A 与 P 的中心不同，G 中的实际素数限制、转换质量及 (K/4) 仍保留。第 106 行整块、430+11 的整真计数及同一系数上的 PP 分布均无新全行结论。未见要求更换本包七源的确定静态缺陷。未运行 Lean/Lake/LSP、守卫或数值证书。本包没有完整黄色职责转蓝，也没有新增绿色。远端应先装好冻结前件与原生依赖，再核七份模块、两个终端及传递导入。
