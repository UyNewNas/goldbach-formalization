# T21 · 实际查询如何共用一个分片

以下是数学说明，区别于已写的 Lean 候选终端。记原冻结精度为 n，辅助根格为 m₀，原来解读 Program 的坐标格为 m₁；下面的平滑精度 s 是另一个参数。增加 s 不改变 n、τ、m₀、m₁、前缀 cap、原表或 Q。

**查询与坐标。** 先取一条原 U3/U4 的发出路径。它的本原空间是一根坐标，加上路径上每条边的 0、1 或 2 个新增坐标。没有把 fixed/retained 的填充 1 当作素数积分；双素数边的本原坐标为（小，大），原整数词按（大，小）追加。父请求的 root、mode、物理节点、累计 d、Q、g 和 read 都由同一条有标记的路径给出。有限类型的预先枚举是根种类、深度、StepShape 串、原 RootKey、原 Program、原 mode、前代、选中单元、胜者、401 个原始 open/knot atom；这里绝不枚举随 N 增长的实际列表位置。对一个含非几何条件的访问，把整除、prime、E 及收据测试留在原离散求和上，不把这些测试改成光滑函数。

在该空间，对每一维取已有光滑一维网格的 label（扩展到 [-1,2]，平台包含闭区间 [0,1]）；取乘积 φⱼ，它在 [0,1]ⁿ 非负且和为 1。不同原有测试若已有不同精度，则对同一物理维度逐项相乘。任一因子用树地址投影，其他因子分别求和，每一步都是 Σφ=1，所以旧测试的每个线性读数逐点保持。重复因子也保留不同地址。对一个实际网格精度 s，非零标签的坐标直径小于 4/(s+1)。在旧计划上再乘这么一个细因子，非零支集只会缩小。没有要求原来的单项误差对任意新 cap 或任意新测试单调。

**前缀。** 写 I 为所有本原坐标，Iₜ 为根与前 t 条边的有效坐标，余者为 Jₜ。固定 a∈labels^Iₜ。对实际发出路径 x，有

    Σ_{b∈labels^Jₜ} φ_{a⊔b}(x) = φ_a(x|Iₜ) · Π_{k∈Jₜ} Σ_c φ_c(x_k) = φ_a(x|Iₜ).

这正是 emitted_native_prefix_marginal，作用于同一 native tuple；无需把双素数两种读序逐坐标判作相同。取多个 t 可重复应用，组成一棵因果细化树。独立的 actual_prefix_marginal 用原 chronological old word 再给一份等式。父 cap 仍只读已出现的槽；新 child 的 LocalDomain 在同一个父 cap/Q 上重新测试。旧词的阈值、owner、retained specified cell 不是 child 重新挑选的变量。把未来标签边缘化不会自动把一个含未来变量的不等式转成任意单一 child 的估计。

**把 sharp 几何查询改为同一计划的上下函数。** 对本原立方体上每个确定的测试集 D，标记每个非零盒是否碰到 D、是否还碰到补集。只碰 D 的权重之和 S，碰 D 的上和 U，双碰之和 M，给出 S≤1_D≤U 及 U−S=M，逐点成立，包括结构等号及真正的整数端点。一个 root/owner 查询用原四分量 keyAt、固定 Program、固定 mode/selected action 与完整 QueryMember 的交集；emitted_owned_iff 在实际点证明它确实是原谓词。只读最终 atom 时使用 emitted_query_iff。不须事先许可包含某个 root owner 的全部整数是一个笛卡尔盒。所有测试共享同一份 φ；每个 D 有自己的 0/1 系数。

**固定几何图的共同绝对误差（书面，结合 T23）。** 先固定上述 n、τ、m₀、m₁。对有限、固定的每个几何测试（含实际 key、winner 及 Member 条件），在根分支、固定 cap 代码、除数符号、max/min 分支、atom 上分片；布尔条件都是有限的有理比较或固定整数表项的比较。实际 resolve 读取唯一的 open/knot atom 或 specified cell，所以 winner 条件也只是这些已有区域的有限并。若暂时离开正分母域，可将分母等于零另作一片按 Lean/原公式的字面值判断；实际获准路径必在正分母片内。片内清分母。**恒等为零的多项式按原严格/弱/相等的真值计算**；例如根 clamp=2 的整开区域可有正质量，inherit 的旧决策保持，不能移入坏集。其余实际界面包含于有限个非零多项式的零集及有限网格端面；按一个变量展开，把所有系数都为零的例外集归纳处理，其余切片有限，Fubini 给零体积。在冻结图上对所有测试取有限并 Γ。这是对固定来源、网格及代的证明，不是跨 n 任意 winner 不变的断言。

若在 x∈[0,1]^r 有 M(x)>0，同一平滑盒有相反真值的点；x 与其中一个相反点的每一维距离都小于 4/(s+1)。连接两点的线段留在原立方体，必须遇到相对边界。故 M(x)≤1_{dist∞(x,Γ)≤4/(s+1)}；对 join 用其细因子。T23 的原完整几何 Member 给 F=(11/384)/101^440≤L≤1/2，每个实际启用素数的指数都在 [b,1]，b=min(a,F/6)>0。取 s 足够大时，只须考虑 [b/2,1]^r。有限个 Γ 的闭邻域体积趋零；用外矩形覆盖可使各 shape 的加权总体积之和任意小。加权常数包括本原密度 ≤4/(F b^r)、有限个测试/shape 及原有界系数，不取 N 依赖的最大值。

把同一估计推回真实归一 Θ/H(N)，此段限于**偶数 N≥2、0≤τ≤1/12、1/(n+1)≤11/384，且 p 属于原 rootFibre N n m₀ k τ c**。给定该根发出的实际路径，用原 rootHistory_catalog 构造真实几何 label；再由根种类、该 fibre 和 T23.mem_ownedMembers 得 h∈ownedMembers。仅有 rootBand 而未经这一步不足以使用 T23。对这个 h，T23.owned_theta_density 给原词 d、同一 cellQ 下 θ/H(N)=ℓ_N(4/L)·Π a(dᵢ₋₁,pᵢ)，首次为 1/(p−2)，重复为 1/p。在 p≥N^b 上，相对调和乘积的逐词因子夹在 1 与 (1+4/N^b)^r 之间。对已选的有限矩形外覆盖，调和素数矩形和趋向 Π dxᵢ/xᵢ；p|N 的删项在每维总计 O(log N/N^b)，其余维有界。在**固定根及 shape** 的发出路径上，每个有效素数 tuple 决定至多一个该深度位置：固定/retained 是唯一的已选位置，各 prime/pair 来自相应无重复 Finset.toList，W2 不同 piece 用不同 shape；对 path 长度归纳。故原 path mark≤1 在这个范围支配绝对误差。不同根和形状分开计数，再在固定有限族取一个 N_geom。τ、n 若需逼近理想，只能先按 T23 对相同几何 Member 的绝对控制选定，然后在冻结对象上运行上面的细分；若前后改变 **实际** winner 或 count，另需证明其比较。

这给的是**共同的外归一绝对界**。任意有界乘子可在已被该绝对包络支配的项上使用；某一极小子族可把全部质量放在坏墙上，因此不推出相对该子族自己的 Θ 也是 o(1)。T23 给了一个来自实际根 transport 的反例。对 fixed owner 的全节 Γ 证明不能替代 arithmetic receiver/base 的重数支配；后者可能有许多 token 对着同一个几何 tuple。几何零质量推 H(N) 尺度上的绝对小量，不等于每个 N 的计数为零。

**一个真正支付新增坐标的行。** 对选中 Buchstab 行，令 d 为原词乘积，L=log_N(Q/d)，c 为原物理 start，j 是新增素数的标签。标准化积分的测试是 residualSingle(u)φⱼ(Lu)，因为 φ 作用在物理 log_N(q) 上。把原 dilation kernel 乘以 φⱼ(物理坐标)，用原 compact_uniform_sandwich 在 [F,G]×[1,6] 上得到 N₁；c>6 时按原 capping 恒等式处理。原 localPrimeFactor 处理首次/重复；原 prefixMask 对此有界测试从 primeWindow N 转至 primeWindow(dN)。在 closedChildren 上，由 natural_atom_iff 的双向几何准入及 thetaAtom_single 的逐素数等式，原 closed Child 和精确等于 θ_parent · 该 masked sum。原 signed_ceiling_error_le 对任何绝对值≤1 的 onAtom 测试给 ≤(4/A)θ_parent，选 A=max(4,8/e) 并取原一致 primeFloor 阈值。因此是原严格 singleChildren、两种 polarities 的估计，不是另一个 prime measure。父的 1≤argument 用真正的 selected_buchstab_guard（给 2≤argument）导出，directionGuard 来自 coherent+selected。

设 M=#(FloorAtom×子标签)，C=1+immutable430AtomL1。每项先取 e=δ/((M+1)C)，再对两个方向及这些固定指标取共同阈值。实际第 g 代的 |oldAtomValue|≤C（原有限范数 envelope），先逐项绝对值再加，得 all_strict_requested 的 ≤δ θ_parent。乘真实非负父 mask×mark，或求和，不产生与子标签数成正比的遗漏。当 θ_parent=0，非负左侧恰为零；未使用 θ_parent 的倒数。这个证明依靠一维 Buchstab 的真实窗和上界纤维；W1/W2 的其他门、双槽和 switched 基项不能继承同一结论。

**最终量词与未付处。** 已供应范围是：reserve → δ 与 (7/2)δ(12^441−1)/11<reserve → 固定原几何/粗 cap → 选择或 overlay 一个足够细的光滑计划 → max(N_geom,N_parent,N_strictBuchstab)。后两个的共同构造为 reserve_common（任意计划 P 则直接对 uniform_feedback 与 all_strict_requested 取 max）；N_geom 的证明在本文和 T23，非 Lean 终端。它们可共享精度，但同一 Buchstab 项只用精细估计一次；若相加两个不同误差，须先分配 δ（例如各 δ/2）。固定有限图上的精度选取与无穷多 N 依赖位置的阈值选取截然不同。

没有从上述 N 导出一个涵盖原十一项后续和 430 条分支上**全部**原计数/叶不等式的 N₀：W1/W2 新子标签下的真实行与 ordinary/positive-switching bases、rejected/control 收据及其原相对符号、各叶政策/截尾和采用的同一 E 必须在这份已有的 prefix/root data 上回测。把 N 依赖的请求列表求最大、把旧 aggregate 容许误差无条件分给任意新子族、或为两边再各选一个 Q，都不能补上这一步。
