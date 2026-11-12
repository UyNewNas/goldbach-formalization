# P2 第二次远端编译失败与五份 R3 修订

五份修订均可按限定清单发表为源码。实际 run 43157098719、job 131037081814、commit 384d2d9070b3af90d95933e08eef964f7b1f7a64 在第 12 步编译失败。逐条核对 205734 字节完整日志，SHA256 为 7dfe74f2bdf40f668dd0ccc946f88adf2cdec05c74a6109c28635017f3bc8eeb。五模块的 17 条带源码行号错误与作者索引完全一致。前一轮四个 R2 修订模块在该次确有 Built 行。编译后的 kernel 与全类型/传递公理步骤跳过；运行时和失败证据留存单独通过。此次独审仅使用本地日志与源对象，没有下载大体积的失败产物。

| 实际失败位置 | 新源码修订及原结论 |
| --- | --- |
| P4AOriginalSeedRange32Invariant 104、145、146、200、288、295 | 保留未替换的原 a,b 证明相邻严格顺序，然后沿有序对等式返回。按 Mathlib 真实命题给 Finset.mem_sort 显式传 ≤。在切分自身坐标用 Function.update_self，真实 min/max 保持。有限三维坐标的最后分支用原 seedLower/Upper 在 2 处的 rfl 等式取得原 z，再应用原不跨 μ 结论。 |
| P4ASixTentRange32Moments 104、245、248 | 固定 Fin 向量上用 Matrix.tail_cons 和 head_cons 消除未化简的 z 表达式，由 ring 整理相同有理式。正界以 Int.cast_one 对齐 Int.le_floor 的前件，再按本轮已经 Built 的 R2 原零分支表达式证明。原 256 项枚举、ln32 执行定义及资源设置保持。 |
| ActualThirdOriginalP4AOrdinaryBCandidateLeaf 138、143、197、259 | 对已证 x、y 两个上界各乘非负 128，由原 μ=25/128 得两整点不等式。保留原 z>0 和所有 B 门。保存表的 query 参数用任意整数 u,D 的有理除法转实数，再单独对齐 P160 的实数标度。显式展开原 realBox 将 hμ 输送至原调用位置。 |
| ActualThirdOriginalSixTentOrdinaryMassCeil 96、171 | 先把 Fin 2 在 0、1 处的 castSucc 改写为 Fin 3 的 0、1，使原 enclosure 的完整左右乘法能按原质量等式重写。query 端沿相同的整数比值和 P160 标度转换，保留原四倍普通质量、上端读数与 ceil。 |
| ActualThirdOriginalRoundedStoredQueryIntegerConsumer 62 | field_simp 已能关闭此次实际等式，后继 ring 仅对剩余目标施行。原 stored grid 整点与分母未改。 |

五份原输入均与前述实际作业 manifest 6d876300c58ee32a2204198142e6863b2c23d2929cab4b1641ca06d551d6714b 和 eb035a259f2f40853e9899f6d98af25852184fee 的对应 Git 原件逐字相等。复算五个独立 diff 与合并 diff，77 个原定理完整头、28 个原定义、进口和证明外全部文本保持。作者登记的固定 Mathlib sort、向量和有理强制转换四个源也按原始 SHA 和 Git blob 对照。另三份 reference 文件确为同一基线中的既有上下文，限定为溯源。作者 REGISTRY 为 9d78b924cb436bcc2c5b86488f1bc28d95d6d420159a2134a48368b9fee9ce08，FREEZE 为 c2d1c87e7116e4b9d640bf04364ed6225efbf183739120c14fb7e8fdacc551ee。

新选本仍需完整 102 模块的编译、逐模块内核、完整声明归属与类型/传递公理和运行时验收。原 101 模块 ABI 自然闭包和单独加入的 FinitePiIntegral 审计均须保留。旧 P4 在该模块的归属集合比较失败，R2 编译提前终止，没有取得新的该模块审计结果。真实模板 46eedd90437fae00921f2a5a6a39abb5996125f45033b230c17d1403d16eec95 已会在不等时先打印并 flush 两个原名称数组、extra 名称、逐名两侧重数、loaded occurrences 和 canonical owner，再执行原 throw。失败 stdout 由 tee 保存在 batch-types.log，随后有 always 上传。下一次沿用原门及诊断即可。

P2_REPAIR_R3_SCOPED_ALLOWLIST.json 的 SHA256 为 dfd9a5c631f5ccc492ae43f8df89bb9e11823765d0a17c1e7d079ebfd00eaf42。29 个可发表文件合计 425149 字节。新运行的数学选本为五个 R3 后像、四个旧 R2 后像、一个旧 ABI 与其余 92 个 eb035 基线模块。未授对象复用或新的绿色职责。

