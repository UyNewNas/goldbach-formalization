# 第二批 coefficient 独立源码验收

2026-10-28，reviewer `/root/manuscript_map`。五项均为 **SOURCE_REVIEW_PASS**，限下表列明的实际源码增量。形式化主目标仍 **OPEN**；未编译、未执行 finite `decide`，formal/kernel credit 均为 **0**，不能据此安装或宣称内核接受。

已读五份冻结 Lean、REGISTRY、REPORT、第二批 TASKS 的原目标、必要前驱及手稿锚点。5 份 candidate SHA 全匹配；登记的 58 项非空 dependency/paper/manifest/archive SHA 检查全匹配，机器记录见 `coefficient.json`。archive 只做字节 hash，没有执行 payload checker。未审计完整传递证明闭包，也未检查 Mathlib API/编译可用性。第二批未另派代理。

| 任务 | 判定 | 实际接受范围 |
| --- | --- | --- |
| coefficient_signed | SOURCE_REVIEW_PASS | unrestricted squarefree raw 的真正 retained 反向覆盖、唯一 k、包括 W 的固定秩穷尽，以及 functional/逐点系数投影等式 |
| coefficient_physical | SOURCE_REVIEW_PASS | 实际 H3 根叶到 q 的唯一 small-factor/leaf fibre、局部 rho 的精确 global mask、signed test 重索引及 active q 的同叶祖先 guard |
| coefficient_rosser | SOURCE_REVIEW_PASS | wire geometry soundness、实际第五 noninitial 值推出第三 supported、unsupported 精确 initial fallback、显式 wire policy 的完整 same-rho source split |
| coefficient_rough | SOURCE_REVIEW_PASS | 实际 Gamma 误差到正向 H5 门槛、literal fifth integer decision，以及同载体 sublist 和上游 first-four licence 下的 retained six-label leaf 构造 |
| coefficient_bv | SOURCE_REVIEW_PASS | 实际 compact upper attached rho 的 low/high 精确分解、high active rank≥3 见证、initial identity 和真实 ordinary BV caller |

## coefficient_signed

`P5All16SquarefreeRawProjection.lean`，SHA `c1d439b2461f6a7f43a1ddba5a3b6bb31d4b0204e8315ea37b300755367e1116`。

39–110 行先由 raw Cartesian 素数词与 squarefree 产品得到无重复、精确 `k=primeFactors.card`，并证明产品整除原始 rough universe 的乘积。literal rawUpperGate 通过既有 `retained_rough_iff_divisor_upper` 反向构造真实 retained support；canonicalSlots 给另一方向，包括 `d=1`。这不是把 support 等价性改成新假设。

130–175 行将未过 gate 的 raw 项按原 weight 自身为零消去；同一 squarefree d 仅在唯一秩贡献。180–226 行用真实 native active mark 和完整 `ordinaryTuples` 的 `mark_modulus_cap`，含 W 分支，得到 `d<N^(153/256)`；每个 rough prime 至少 `N^rho`，故固定界 `floor((5/8)/rho)` 先于 N、t。未把所需 rank bound 当输入，也未错误套用旧 non-W 引理。

232–310 行保留同一 E、beta、marked scalar 和 signed F，证明全 k squarefree functional 等于实际 `jointPresievedSigma`，再得 owner functional 及逐点系数等式。剩余恰是已定义的 signed repeated-rough kernel。最终元数据按原完整任务口径保持 `task_complete=false`，本批有限反向覆盖/秩穷尽的证明文本以 `local_step_complete=true`、`batch_target_source_complete=true` 记录；没有整个 PP 完成信用。

最终元数据 guard 已核对：REGISTRY SHA `05d0bf7059e490561c77b2c9d9d3424125441453ceb3cd7a0f8bb676670188b4`，REPORT SHA `0f561798d9e852ffc1b3d6190cb269655fb2cd5952c518d8820c9b4acedff3e2`；Lean 字节及上述源码判定不变。

仍需实例化实际 `w=N^rho≤Z` 参数许可、sorted owner/block regroup、count/mean 各自的 absolute collision saving、解析 PP 及编译验收。

## coefficient_physical

`P5OriginalH3LocalPhysicalQFibre.lean`，SHA `35a9e4117279b9c3d9efdc33be733cbff63afaaebc559dd999231c5e8994de02`。

38–101 行把 H3 条件放在**该实际 retained 根叶自身**的第八祖先上，定义真实小因子/叶 pair 及其自然 q 像。113–220 行结合严格 small/rough 唯一性与 retained leaf-product 单射，证明 q 确定唯一 pair，且 betaPlus/betaMinus 来自同一叶真实符号。222–300 行证明 localRho 是 global `actualSmallRoughRho` 在该精确 q 像上的 mask；任意 signed F 无重数地重索引，非零 local q 反向取得唯一叶、`a<L` 和该叶祖先的 H3 guard/mask/newCap。它修补了第一批仅有“某 pre 的 cap + 任意 q 全局 support”的合取。

303–313 行专门化到 literal physicalRho。**拓扑边界保持明确：**使用的根叶是 `oddFirstExitPolicy retainOdd`，正是 fixedRoughSupport 的定义；没有证明它等于任意完整 Bool policy 的叶。局部集合未被证明非空，全球祖先供应、87 域覆盖/不交、积分收益与 K 继续开放，不能给这些范围记信用。

## coefficient_rosser

`P1Pair12ActualWireSourceSupport.lean`，SHA `43cd3261e541aa055fe8b1253054dea508e76ad8ab115fec7064c0a6e195d477`。

37–67 行复用 original rational wire checker soundness 与第一批 numeric-mask 字典。显示的 row0 是一个具体 finite `by decide` 证明项；NPZ hash 匹配只给静态出处，未执行此证明，也没有形式化 archive membership/全 370 万行通过结论。

71–139 行从真实第五 eligible cell 的 half-open 父投影及 whole-cell rough 下端点，构造实际第三 selected membership 与自然数 rough activation。143–198 行进一步用所有第四/第五候选的全局上界证明 unsupported 时 inherited4 和 exponent5 都精确等于初始 fallback；所以非初始第五值（包括第四更新继承）能推出 supported。未假定每个 retained pair12 状态都有 support。

204–283 行的 `wirePolicy5` 对完整输入 record bank 使用显式 sourceGeometryFlag。其实际单位权重 arithmetic frontier 的 noninitial pair12 分支消除 caller Geometry/mask/supported 前提；same-rho update 的补集完整保留。**该旗标 policy 与采用的历史 licence 一致性仍未证明**，不能据此声称原历史 gain 保留。完整 archive parse/check、第五 coverage/owner、H5、sixth action、chronology 及 PP/density/K 仍开放。作者的局部完成/整体未完成描述符合源码。

## coefficient_rough

`P2ActualFifthBufferedParentWitness.lean`，SHA `8aaa2b4e4aad76cd179dd15eaf47f7587fa80f158b55df2a66285ede6cc10d16`。

54–100 行从实际 selected third box 的 width≤chi 与 rationalInterval_v_error/baseline_le_gamma 得到 `inherited4≥R0−3chi/2−2e`；原第四、第五 finite maxima 保留该 seed。104–151 行使用 PhysicalCell 的 `H3,H5<R0` 与 `t0<25/128`，证明 parentAllowance 正，且显式共同 history-buffer 前提足以支付实际误差并推出 `H5<actual exponent5`。没有把第一批 ceiling 当存在证明。

159–219 行用 literal 正且严格递减六整数历史的精确 log/rpow 字典给第一、第三、第五整数量方门，并通过 upper-five admissibility 得到实际第五决策。225–255 行保留同载体六标签 sublist 和**上游前四次选择有效**，由新第五决策和 upper 偶数第六自动保留构造真实 retained leaf。没有将第五/第六 retention 放回前提。

这是一份有限条件构造。统一选择 e/chi、selected-third 支持与整个紧集 buffer、实际 adopted prime carrier 的 sublist/first-four licence、source-fibre 与 rough-SW/PP 接口均未闭合。报告诚实保留这些实施义务。

## coefficient_bv

`P1ActualCompactUpperBVBranchSplit.lean`，SHA `35171c1b7a397485ee5ea868018a5e349c1dfda15acd531e601273c9a182e49d`。

28–66 行只定义一次实际 attached upper rho/support，对任意 signed test 分为既有 genuine low-rank subset 与其补集。72–112 行取得实际 active integer factorization `q=a*b`、`a<N^epsilon` 与 rough coefficient 非零；small/rough 唯一性把“并非所有支持分解都 low rank”准确变成同一实际 b 的 rank≥3。115–128 行的 low branch 保持同一 full q 上的 shallow-tree initial coefficient。

133–155 行实际调用冻结 Phase6 supplier。已读 Phase4/6 证明链：对同一 full q 以 `19/48+1/192=77/192<1/2` 支付 small factor，证明 actual active subset、互素性与一有界系数后调用 ordinary prime-AP BV；共同阈值先于 compact policy、mesh、attachment。没有把待证 target estimate 作为前提。

本次 low branch 是原稿 upper **rough-factor rank≤2** 的实际 compact attached coefficient，并非第一批 four-mark joint total-rank≤2 空类。源码未证明某个具体数值 owner/族非空，故不给该项信用；caller 的证明也不依赖空类排除。高秩解析、marked graph-to-integer、generalized convolution/prime-product caller 与完整 PP 继续开放，报告没有超报。

五项均未发现循环 final-target 假设或新的原稿数学反例。仅写本目录的 `coefficient.json` 与本文件；第一批、作者交付和生产源码均未修改。
