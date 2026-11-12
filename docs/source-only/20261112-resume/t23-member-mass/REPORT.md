# T23 / Y24 — 全部几何 Member、原生截面与有序前缀 Θ

**冻结：SOURCE_ONLY / UNCOMPILED / 独审待判。原始计数意义的整个 Y24、h34 未闭合。** 本包的“完整”指原 U3、U4 rootFibre 上所有满足原递归 Member 的几何标签，而非某个 generated 子集。它不把所有备选 Program 加作原计数。仅写 T23 目录，未运行 Lean/Lake/LSP/guard/数值 producer、证书、远端或 CI。

原稿为 chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b，paper/source/manuscript-body.tex:795–817,823–877,887–892；佐证 proof-library/source/global-chen-lower-completion-20261010.txt 第 3、4 节。795–805 要求同一 Q 的正标记平均，865–877 规定 reserve 后选择共同近似和零质量绝对误差。工作基准 3d15576a2eb00ba03deb3cf54f170c0a7f91c1f9；补充 P5 快照 001d139e667eb5cb42f1e9ca8f02de221b00db5c 的算术 Buchstab 内层与首尾、完整整数 catalog 均已复用，不重做。T11 清单与 S28 FINAL_CHECKPOINT_WHOLE_SCOPE_HOLD 为责任基准。输入 Git blobs、原始 bytes SHA 见 REGISTRY。

## 提交的 Lean 源码

1. **OwnedMemberMass.** ownedMembers 是既有 univ.filter Valid 的 catalog 再筛两个原始根条件：根种类恰为 k，原始素数恰在 rootFibre N n m k τ c。Valid 穷举深度 0…440、原始 Program、各 active 素数，dummy 只许 1，并含全部递归 Member。没有 winning-action、chosen-history 或 Buchstab direction 假设。U3、U4 重叠仍以原标签重复；none owner 保留。一标签在唯一 k,c 中（rootFibre 是 keyAt 的 fibre）。history_support 给词、真 α、同 Q 和下界；member_residual_le_root 由每次新增正的实际坐标得出。故 owned_support 从每个完整实际几何历史给出固定紧区间 F ≤ L ≤ 1/2，其中 F=(11/384)/101^440，同时 Q=d N^L 且 (1−log_N d)/L≥2。理想根复用 actual430_residual_floor 的更大下界，441 个顶点之间至多 440 次转移。
2. **同一根 Fibre 的绝对误差。** uniform_owned_member_rows 为每个完整父标签选择一个 106-bank 行或父极性的 Buchstab 行；旧代取 Fin 430。先用 S18 singleton 实际算术父行逐原子取绝对值，再乘非负 mark 相加；不是把 signed profile 小误差推到任意子族。两向 Buchstab 直接用 immutable430_uniform_buchstab_rows（含原严格整数窗口、moving start 和 ceiling 付款）。未激活 lower 方向的整数行为空，父 Θ 仍在；见 inactive_buchstab_row_zero。结果 ownedError≤ε·ownedTheta，若 ownedTheta=0 则 ownedError=0。uniform_outer_owned_error 加总两个原标签及全 RootKey，各自保留自己的 Q，阈值先于 N,n,m,mesh,g、动作和标记。该阈值仅属算术局部行。bank 分支给既有实际 feedback 算术载体，不宣称这个动作可在每个父采纳；新 child 的 gate、原母计数、base 均未经筛选。
3. **NativeProperSections.** fresh_coordinate_floor 从实际 LocalDomain 导出每个新增有效 x≥L/6，不积分占位坐标。numerator_section、section_zero_iff 对五类 active query 给出真正的 native affine pivot；active_knot_section_null 对切片给零测，active_strip_integral_tendsto 给含等号的**闭** strip 对任意可积切片密度的绝对 L¹ 消退。R14 的同词 inherit、root-clamp、401 atoms、变量 arity 可测已有，不重复。下面的全路径 Fubini/DCT 拼接是数学证明，不是已实现的 Lean 终端。
4. **OwnedThetaWord.** 真实有序素数词 p₁,…,pᵣ，前缀 dᵢ=∏_{j≤i}pⱼ。owned_theta_density 给出 θ_N(Q,dᵣ)/H(N) = ℓ_N·(4/L)·∏ᵢ a(dᵢ₋₁,pᵢ)，其中 ℓ_N=li(N)log N/N，a(d,p) 在重复 p|d 时为 1/p，首次时为 1/(p−2)。由原始 singular/totient 插入恒等式、实际 residual log 与 T07 原归一化得出。word_to_harmonic 给所有 pᵢ≥A≥4 时 1≤dᵣ∏a≤(1+4/A)^r，没有删除重复。history_mark_le_one 由原 edgeWeight 给每一实际位置的 mark≤1；并非所有同标签位置的总 mark≤1。

## 完整原生几何域的书面证明

固定根种类和有限 shape itinerary。原生空间维数 r=1+∑arity≤881。使用 R14 的 nativeProgram、nativeCoordinates、QueryMember；固定 Program 时额外测试其不动 cell。D 表理想完整域，Dₙ 表 frozen(n,finiteTau n) 完整域，前后用相同实际原生坐标。每次取原有限格的一个 atom；不随 n 改写格点。完整行表来自 MemberGateRows.localRows。若当前前缀有累计新坐标 Σx，则 L=L₀(t)−Σx；C 为最后一批加入的较小素数指数，未加入时 C=t。L₀ 在真根分支取 (1−t)/2、57/64−5t/2、1/2−t 中相应项。

| 行 | proper 的自由切片变量 | 具有正质量的等号或继承 |
|---|---|---|
| 根带、cell、incomingAllowed、正坐标、顺序、C−x 或 C−y | 固定根/当次 fresh 坐标（有需要时） | ideal/frozen 使用同一词，静态 gate 真值相同，弱等号保留 |
| L>0；L−2x、L−2y、L−y−2x；严格 bank endpoints x−cL、c′L−x 等 | 前缀已准入时 L≥F；余者对一个当次 fresh 坐标斜率非零 | 保留实际 strict/weak；体积零不等于算术 endpoint 为空 |
| Buchstab 的 L−3x、L−sx、6x−L | 当次 x，因 s≥1 三项均有非零斜率 | lower 另测试 s≥2，不丢结构 s=2 |
| parent query 与常数的比较、终端 knot/guard | 找最近一次设置 query 的步骤。Buchstab 分子 L−(c+1)x；W1/W2 单步 (s₀−c)L−s₀x；W2 固定小 x 时为 (s₀−c)L−s₀(x+y) 或 L−(c+1)x−y。native 大 y 斜率非零 | retain 继承。固定比较、transport 重置为同一常数。若最后设置在根，非钳位分支是 L₀(t)/a；理想钳位 s=2 在只向下冻结时恰保持，整片保留，绝非只留零测边缘 |
| parent cap cC−L，c 为正的 bank 常数 | 有 fresh 历史则变动最后加入的最小 x，斜率 c+1；未追加则 ct−L₀(t) 的斜率正 | 相同 prefix 的 CapPlan/inherit 用 R14 actual_same_prefix_choices，不能在子节点重选祖先 cap |

每个 proper 截面对其余坐标固定时至多一解，有限个根分支端点另计；若零集涉及以前的 active 查询，可切以前的 pivot 坐标，后续约束只限制该零集的子集。Fubini 给有限并零体积。用第一处分歧归纳而非假设整程共同准入：两边相同的静态 gate 同失败或同通过；前缀共同通过后 residual/argument 收敛，非零 proper 值最终同号；所有结构等号依表精确保持。首次不同 gate 若未落在这些边界，有限深度内最终不可能。由此 1_{Dₙ}→1_D a.e.，含完整终端过滤而非仅最后的 LocalDomain。对 401 个 atoms 可取有限并。

在理想或冻结一侧准入的路径上，任一启用素数指数均 ≥b=min(a,F/6)>0（Buchstab 的 w≤5；bank 的单、双归一化坐标≥1/5）。都 ≤1。完整原生密度 W=4/(L∏xᵢ)，冻结 Wₙ 同式用实际 Lₙ；两侧各自延零，均受 [b,1]^r 上 4/(Fb^r) 控制。R14 提供 joint measurability；实际词不变且 Lₙ→L。于是 DCT 给

**∫ |1_{Dₙ}Wₙ − 1_D W| dx → 0。**

这是同一 native x 上两个完整域密度的绝对差。对 Buchstab 子坐标的系数换元，复用 R15 nativeAtomCoefficient_eq，分别使用各自 x=L/(w+1)；不假两种 parent 的换元相同。完整根幅度 A−H430 复用 R15 full-root amplitude L¹；clamp 处的幅度读点精确相同。此证明不估 ordinary/switched bases。固定有限形状及所有具体原格测试可在这里取共同精度；没有因此构造 T21 的 nested 441。

## 归一化算术 Θ 与绝对误差

在 cube 取 A=N^b；有序词的相对乘积因子相对 ∏1/p 的偏差 ≤(1+4/N^b)^r−1→0，逐点有效。ℓ_N→1 见 T07 RootIntervalTheta。固定 n 后，把实际 arithmetic Member 的 θ/H(N) 替换为调和素数乘积测度对 4/L 的积分：误差一致小乘以 cube 的有界质量（每维 ∑_{N^b≤p≤N}1/p=O_b(1)）。对理想侧使用真根 Q=N^λ 与相同 inserted_word 和 L=log(Q/d)/log N 代数即可。理想/frozen 单侧差在该侧获准的域上作同样比较，不使用未准入侧的倒数上界。

固定 n，矩形调和素数和给极限 ∏dxᵢ/xᵢ。项目既有 tendsto_actualPrimeBoxTestSum_cube 直接处理连续测试；对本处的扩张：全部域在正分母片上的条件是有限的有理不等式，故有界被积函数除零体积集外连续。具体地，按根分支及有限 rootCode 台阶分片；每片清分母后，非零多项式的零集为零（按最后变量展开、归纳非零最高系数的例外集，继以 Fubini）。恒等零多项式在开片上取原来的 strict/weak 布尔值，不能把整片当坏集；根的常总水平亦如此。对全指标绝对差的矩形上下阶梯夹逼给相同极限。剔除 p|N 的调和质量每维至多 log₂(N)/N^b；若原严格 child 排除旧前缀重复，重复对 ≤∑_{p≥N^b}p⁻²=o(1)，乘其他维有界质量。以上只比较 Θ，不是 T19 未筛母计数的付款；若原域保留重复，精确公式本已包含。

所以先固定 n 取偶 N→∞，再取 n→∞，完整几何域归一化绝对差的 limsup 为 0。对同一 integrand 的互斥 RootKey 分割可先取逐位置绝对值再加总，各 Q 不混写。若 0≤m_N(tuple)≤M，给绝对差乘该标记的损失至多 M 倍整域损失，不必假标记本身收敛；这不是任意子族相对其自身 Θ 的估计。理想零质量片因此仍有占 H(N) 的绝对 o(1)；与 Lean 上 actual ownedTheta=0 推出 exact ownedError=0 是两个不同命题。若原 receiver multiplicity 或源位置在同一几何 tuple 上汇合，需要证明累计支配，或直接在已计数的位置上比较；单个路径 mark≤1 不能替代它。

**位置重数的一个可证范围（书面）。** 对源码 RequestedBranches.children、RequestedHistory.history 生成的那个固定根 request、固定 430 深度上限的反馈树，固定一条完整 shape 串及其 active prime tuple，一定深度的列表位置至多一个。归纳路径：空串只可能是列表头 origin。非空串的第一个 shape 和实际原生素数在父 request 上至多给一个 child 位置：resolve 无值时没有 children；若 retained，尽管 edgeShape 忘掉 i，真实父 resolve 的 i 已唯一且列表是单元；若 Buchstab 或 W1 prime，素数 Finset.toList 无重复；W2 的两个固定 anchor、三种 singleton piece、四种 pair piece 都有不同 shape，piece 内的 prime 或有序 pair 同样来自无重复 Finset.toList。W1 固定项与 prime 项也有不同 shape。在这个唯一 edge 上 nextRequest 唯一，history.flatMap/map prepend 不会产生第二个有相同余串的后继位置，由归纳完成。因此在固定形状保留原根、代和 active prime tuple 时，真实**已发出反馈路径位置**的单个 mark≤1 可用作前述正包络；不同形状保留标签、按有限并支配。它说明为何不能仅靠 mark≤1 就跳到此结论。该归纳只数反馈列表位置，不数同一位置中可以有很多个的原始 receiver、adopted seed/base 或 switched-product 实例。边界误差是在同一冻结位置上把已知几何域换成另一几何域；若同时改变 winner/mask，或要证明 position marks 本身在理想图和冻结图相同，还需各自相应的比较。

## 一个真实的量词检验

在 U3 增强根取 a=417/5000、几何 .transport 194，gridArgument=1+195/50=4.9。令 t*=1−2a·4.9=4567/25000，处在 a<t<25/128 的 λ(t)=(1+t)/2 分支。对任何足够细且有限的 n，t 从左逼近 t* 时，frozenLevel n (λ(t)) 只取有限个 ≤λ(t)<λ(t*) 的值，故其最大值严格低于 λ(t*)。于是靠 t* 左侧某一开区间上，真实 s=(1−t)/(2a)>4.9，冻结 s<4.9；两侧 residual 都正，incoming upper 合法，transport 真值相反。任意固定该区间，PNT 保证对足够大 N 有原 U3 根素数 p∤N（剔除 O(log N) 个不足影响）。若标记只给其中一根，归一至其**自身** Θ 的 gate 对称差为 1；其唯一 RootKey 不改变这个差异。这否定“任意正子族均有趋零的相对边界损失”的外推；不声称 transport 194 是该根真正选中的 winner，也不否定原稿对整源绝对误差的论证。

## 交接与开放义务

- **形式/API：** 三文件均 source-only，未解析、elaborate、kernel 或传递 axiom 检查。全路径 Fubini/DCT 与 prime-box 延拓是上文的数学证明；列出的 Lean 终端不是整条 L¹ 定理。
- **可补省略：** 对完整几何 Member 的 proper/equality/inherit 分类、共同残差下界与原始外 Θ 的真实逐词公式已在原始实例给出。对 coherent 已选 Buchstab 请求，P5 11月6日 actual_buchstab_physical_trim_eq_zero 已付 trim，不重新列欠账。
- **实质未获供应：** rootHistory_catalog 只证明已生成路径映入几何 catalog；original_U34_eq_owned_root_counts 是根入口。完整几何域并不自动有原稿采用的所有 count/receiver 权重，更不能把 alternative actions 一并加入。T17 的选中 incidence/actual root mask 可在其范围逐位置用；整体 selected/full/inherited count 与本文 Θ 的同源比较、累计 receiver/位置权重、各 true base/seed 及不同模块同一个 430+11 causal realization 仍需另外核证。没有假设 h34、目标 Member mass 或 common N0，未改主稿或黄行。R16/S18/T17、T19、T21 的组件不重复计功。
