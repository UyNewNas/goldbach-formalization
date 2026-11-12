# T18 独审 T23 混合 Member 对称差

**五份冻结源码在连续几何范围内通过。** 对任意固定网格、U3 或 U4 根、至多 440 步的完整 Program、上下表极性和原 401 个原子，理想与冻结 QueryMember 的对称差体积趋零。两侧真物理密度在各自完整集合上延零后，其绝对差积分也趋零。上一轮留在上界中的混合路径对称差现在有无条件源码终端。Y24、Y28 与整体 h34 仍黄，形式信用为 0。

## 如何定位首次不同的原门

- **实际坐标。** 每个 shape 序列的坐标是根 $t$ 和每步实际读取的零、一或两个实变量。FreshAxis 的 avoid_graph 将一个真实槽与其补集分开，使用有限乘积上的保测等价。若可测函数在将该槽改成零时保持原值，则在补集固定后，等式 $x_j=f(x)$ 的该槽截面只有一个点。Fubini 将它提升到整个路径的积测度。MixedNativeWalk 逐步证明理想父状态对所有未读槽均满足这项不变性。任一新槽只在其第一次读取处使用。对 W2 双素数，较小坐标仍参与积分，活动查询等号的最后切片取较大坐标。
- **逐行核对。** MixedGateStability 第 41、107 行使用 R14 的 localDomain_iff_rows。原单、双素数行中可变化的端点由 $z_j=cL$、$z_0=L/s$ 或 $z_1=L-2z_0$ 支付。系数来自各行的真实 W1/W2 窗以及 $1/2,1/3,1/6$。这包括 W2 用较小素数裁切的窗、两种 $y+2x$ 平方符号，以及上下 Buchstab 的移动下界。共享旧词使 ceiling 与静态顺序行逐点相同。原弱 cap $L/c\le C$ 在理想侧取等时，由同一词上的 $L_n\le L$ 逐精度保留。残量为正、$s\in[1,6]$ 的使用均在此前理想 LocalDomain 已准入的守卫内。
- **继承与查表跳点。** 未钳位的根查询在固定值 $c$ 上至多命中三个根坐标。理想根查询钳在 2 时，原向下冻结精确保留 2。retain 继承上一状态的两个方向弱比较，固定 W1/W2 锚及 transport 将两侧重设为同一常数。活动子步使用原 query_knot_comparisons 和非零斜率切片。上、下查询与 open 原子取相应符号，singleton 原子用两个弱比较同时成立识别等号。因此具有正体积的结构等值层也按其原规则进入判定。
- **完整递归。** MixedNativeWalk.walk 第 115 行在同一原生点、同一 shape 和共享的 cell 代码上推进。某一步理想门失败时，冻结方最终也失败。理想门成功时，冻结方最终通过，再接子状态的最终判定。父状态位于相同分支极性，同一 incomingAllowed 与 cellMember 同时出现。终端回到原 QueryMember 的表原子。归纳守卫只依赖已走过的理想 LocalDomain，结论覆盖从任一侧进入对称差的点。

## 体积、双侧物理权与指定 cell

写 $I$、$S_n$ 为理想和冻结的完整 canonical QueryMember，$B=[0,1]^{\mathrm{NativeSlot}}\cap\{t\in\mathrm{rootBand}(k)\}$。可测指标 $1_{I\triangle S_n}$ 在 $B$ 上几乎处处最终为零，并由 1 支配。$B$ 的体积有限，DCT 给出的积分正是 $\operatorname{vol}(B\cap(I\triangle S_n))$。每个有限深度均有这个体积结论。支集包含关系与各侧密度下界使用已审 NativeMovingDensity。深度至多 440 时，$F=(11/384)/101^{440}$、$b=\min(1,a,F/6)$，至多 881 个实际指数的乘积至少 $b^{881}$。两侧分别延零后均可积，且

$$
\int_B|1_IW-1_{S_n}V_n|
\le r_n\,\operatorname{vol}(B)
 + {4\over F b^{881}}\operatorname{vol}(B\cap(I\triangle S_n))
\longrightarrow 0 .
$$

这里 $r_n\to0$ 沿用前包的同一物理权重扰动。以上与 MixedNativeL1 的 mixed_difference_volume、fine_extended_integrable、mixed_full_native_L1 对应。finite_mixed_native_threshold 对固定 mesh 和 $\varepsilon>0$ 同时给出全部有限 shape、根、极性、原子共用的冻结精度下界。

FixedProgramL1 第 45、61、114、154 行进一步识别指定 Program 的真实 cell 所有权。原 cellMember_unique 连同每个坐标准入的 $[0,1]$ 条件，沿已通过路径强制 canonicalProgram 恰等于指定 code。因此两侧各自的 fixedSet 都等于相应 nativeSet 与同一 code 纤维之交，fixedDifference 也恰是原对称差与该纤维之交。realize_eq_of_shapes 将两侧使用的密度识别为指定 code 在原坐标上的真物理密度。在固定网格上，all_fixed_program_threshold 同时控制全部指定 cells 的完整双侧积分与对称差体积。这个判断保留空集合、端点所属 cell 和原根标签。

## 范围与冻结依据

shared_owner_difference 允许同一限制 $O_n$ 施于两侧，因为与它相交的对称差由全域的绝对体积支配。固定 Program 的几何 cell 纤维已由源码识别。若两侧分别重选算术 owner 或 winner，所选集合的差异仍需估计。本轮的共同阈值属于冻结精度 $n$。实际加法素数、接收者和 adopted 权的筛变，及相应整数 $N$ 的共同阈值，仍需离散素数盒或带标记计数的独立输入。按任意集中子族自身 $\Theta$ 取相对误差仍受首包 transport-194 的反例限制。固定根上的两侧比较也未构造原稿不同模块的共同 430+11 实现。

五个 Lean 文件共 47,161 字节。逐项核对冻结 SHA-256、字节数、行数、imports 和公开 theorem，以及 29 条历史依赖、4 条前件冻结记录和 1 条原稿记录的 commit/path、blob、长度、SHA-256。作者登记主快照为 69cb7a2e52f4a8b5ed2f25a725b6cc869b11744b，P5 快照为 001d139e667eb5cb42f1e9ca8f02de221b00db5c，原稿为 9731290e8f53cffda44129906cde6a965eaa869b。本轮核验全用本地源文件与 Git 对象，禁用了 Git 传输协议。此审单为数学与源码静态意见，未运行 Lean。
