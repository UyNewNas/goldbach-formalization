第二批 upper_chronology 已输出 `P4AOriginalCell0HalfOpenPrimeCarrier.lean`。未编译，正式信用为 0；local_step_complete=true，原完整 upper chronology 目标仍 OPEN。

新增的是原始 cell0 的实际半开 carrier，不再从调用者索取96行或 firstStop。`qPoint/qLo/qHi` 使用原有 [0,19/96] 粗网格；每个 affine 行按系数正负选 lo/hi，得到整个闭盒上的精确有理下界。有限 bank 同时检查96个下界严格为正、第0轴上端≤19/96−4e。bank 完全不含 N，先于算术选定。

`primeBox` 是现有实际 prime carrier：每个 p_i 为素数、不整除共同目标 N，并满足 N^lo≤p_i<N^hi。复用原库 exact log/power dictionary，`selectedFrontier` 在原父树真实 rank8 frontier 上按这些实际素数盒成员关系过滤，保留 sign、mass、remaining carrier。由此证明实际长度8、真实父policy admission、全部96行，以及真正 `HistoricalThirdCoarse.firstStop e m N (rosserAncestor 1 pre)`。这个 firstStop 从同一个半开粗标签上端推出，不是先放入选中域再投影。

网格坐标等号按 Ico 的唯一格归属；源码 affine 等号墙则全部落入本 cell0 动作的 inherit 分支。`localCell0Cap_on_wall` 证明精确继承 slot15；`slot15_le_localCell0Cap` 证明有许可时该局部动作是真正增大，未许可时精确继承。`selected_actual_slot16` 将真实有限 carrier 接回前批 slot16 结论，唯一保留的实际几何供应是原 sixth ancestor 的 CurrentParentGuard。

另外证明原源码内点最终能由此有理 bank 接纳：literalRows 给 t0<25/128；e≤1/1536 时自动有 t0<19/96−4e，因为 19/96−25/128=1/384。现有 mesh 两端向点收敛，96个 affine 全盒下界一起收敛到严格正值，第0轴 stop 上端一起满足，遂得一个共同足够细的 mesh。此为每个内点的最终覆盖；未声称已证明整块加权积分误差或固定有限bank的全局reserve。

仍需：真实 all-eleven sixth cap/父历史 guard；单个共同有限分区的加权误差及完整14/58/87源策略身份；same-rho、密度、数值saving及K。原稿未发现新的数学缺口。只做静态源码审阅和哈希登记，没有编译、修编译、运行checker或额度检查。
