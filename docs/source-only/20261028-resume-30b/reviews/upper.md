# 第二批 upper 独立源码验收

四项均为 **SOURCE_REVIEW_PASS**，限于各自局部源码命题；共审5份新 Lean 与4组 REGISTRY/REPORT。`compiled=false`、`kernel_verified=false`、`formal_credit=0`、`task_complete=false`。whole upper、主定理和最终 K 仍为 OPEN。

逐项核对实际源码、必要前驱、原稿与 producer 公式；没有只采信作者报告。5份候选源码哈希和登记的可解析 path/hash 均匹配（含 Jensen 的相邻 payload 精确版本与 Mathlib manifest），详见 `upper.json`。进行的是两父、每父32个父顶点和32个 zeroChild 顶点的小型独立有理核算；没有编译、运行 Lean decide/大型 checker、重放全档案、修编译或查额度。哈希不代表完整依赖/API/内核闭包已被验证。

| 项目 | 结论 | 局部通过范围 |
|---|---|---|
| upper_chronology | SOURCE_REVIEW_PASS | 实际半开 primeBox/frontier、96行与真实 firstStop 供应、局部墙继承 |
| upper_fifth | SOURCE_REVIEW_PASS | 原父 midpoint picks、正确双尺度 d、两实际 zeroChild 的几何输入 |
| upper_mesh | SOURCE_REVIEW_PASS | 真实 literal 可变 kernel 的紧集 supnorm 模量和统一质量界 |
| upper_jensen | SOURCE_REVIEW_PASS | whole-child 正部 surrogate 的 Jensen 积分界及两个实际实例 |

## upper_chronology

`rowLowerQ` 按 affine 系数符号选 lo/hi，确为整个闭盒的下界；bank 在 N 前同时检查96个严格下界和第0轴粗标签上端。`primeBox` 复用实际素数、目标排除和精确 `N^lo<=p<N^hi` 的字典，Ico 网格提供共享端点的唯一归属。`selectedFrontier` 过滤原 rank8 树而保留其状态；从实际长度和祖先坐标恒等式推出真正 rank1 coarse `firstStop`，它没有预先藏在 carrier 前提中。

`19/96-25/128=1/384`，因此 `e<=1/1536` 下 literal `t0<25/128` 给严格 stop margin；各端点收敛和有限96行给每个内点的共同 eventual mesh 接纳。量词是逐点 eventual，不是一个网格已覆盖整开域并支付统一加权误差。affine 等号墙不能通过严格行测试，局部动作精确继承 slot15；许可分支保留真实 sixth `CurrentParentGuard`，由既有 slot16 绑定证明局部不降低 cap。

真实 all-eleven sixth guard、单个固定 bank 的统一加权误差、完整14/58/87身份、same-rho密度/数值/K仍欠；报告准确保留这些欠项。

## upper_fifth

父 midpoint 的 A/C/cap 按先后 argmin 选择，grid400 的同一正倍率 `64*n` 与 producer 三列整数分数一致。picks 在全部 children 固定。十五平面/B 最大值及 `max(U_P,S5+2t5)` 的有理表达式精确 cast 到相同真实 `frozenGap/vertexD`，没有更换旧比较基线。

独立 Fraction 核算复现两个父的 picks `[0,0,0,0,0,0,1,0,0,0,1,0,1,1,1]`、grid400父 d=5984/5232，以及 widths=(2,2,2,2,1)、grid1600 zeroChild d=29824/25152。两种 `32*n` 标准化没有混用。父0用 A、父1用 C，从实际 lower endpoints 证明 residual 分别<=4、<=399/100；childLeft 正性与所有闭 child 比率界均有供应。zeroChild gap 积分下界消费新 hd 恒等式，没有把所求积分当假设。

NPZ 字节绑定、其余63 children/完整历史父集、log/Q80 floor、selected-owner clipping、buffered tree 和 K仍欠；有限 Lean decide 尚未执行，未计正式信用。

## upper_mesh

同一 saved mask 仍定义 `M_I(t)-2e`，旧项是 tuple-dependent `rawFourth(t)-2e`。真实 canonical 零延拓消解严格 own-cube 等号面的表观跳跃；正紧立方体 K=[1/400,19/96]^5 上的所有倒数有正下界。因此得到(e,t)联合连续和 `C(K,R)` 的真实 supnorm 连续族。

`rowModulus(e)=norm(f_e-f_0)` 连续、在0为0、非负且逐点控制 kernel 差。对 buffer 紧区间再取连续映射范数，`rowMassBound=max(1,norm(bufferFamily))` 控制所有 e/t，不依赖 q 或 child 数。实际 `rawOwnerDomain` 进入同一 K 来自 grid400 和 lower keys>=1 的真实子集定理。

这里供应的是保守 literal kernel 的模量，不宣称等于任意 licensed actual old4；报告明确保留该边界。actual selected/firstStop 截面界、B13实际逐行积分误差、全档案 verdict/omitted trim、full87祖先与 reserves仍欠。

## upper_jensen

从实际闭 child 的 residual<=b 与 frozen ceiling>=S5+2t5 得 `g_+<=(b-2)t5`。由于 `0<t5<=T`，`X=g_+/T<=g_+/t5`，两者均在准确区间[0,b-2]。结合真实32顶点 gap 积分下界和几何上界，推出 `e=d/(1024*1600*T)` 的合法范围；没有假设所需均值、Q范围或核积分。

平均值方向为 `average X>=e`，再用 Q递增及凸Jensen：`Q(e)<=Q(average X)<=average Q(X)`。child 常数幅度 `A=(4/T)*prod(1/right_i)` 非负且不超过逐点幅度；Q非负使比较方向成立。moving profile 零延拓连续提供可积性，乘以正体积 V 后正确消去归一化，得到 `integral kernel>=V*A*Q(e)`。

整数尺度为 `V*A=4*1600*prod(width)/(h5*prod(h_i))`、`e=d/(1024*h5)`。两无额外前提实例精确消费相邻冻结 payload，得到 `(b,e)=(4,233/808)` 和 `(399/100,393/1616)`，与独立32顶点核算一致。依赖方向没有循环：实例模块消费 payload/general theorem，payload 未导入新 Jensen 模块。

积分始终是 **whole-child、unbuffered、positive frozen-parent surrogate**；没有用它替换 signed literal kernel 或实际 selected-owner 剪裁贡献。clipping-loss、全行/child、atanh/log/Q80 floor、汇总 reserves 和当前 K仍欠。四项 `local_step_complete` 仅在以上窄范围有源码支持，均不构成广义任务完成。
