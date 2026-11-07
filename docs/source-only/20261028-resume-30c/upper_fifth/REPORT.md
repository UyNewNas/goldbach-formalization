# upper_fifth 第三批：两 named parent 的全部64子盒

新增 `P5NamedFifthAllChildren.lean`。前两批冻结未改；本批只读原稿和源码，未编译、未执行 Lean `decide`、未运行 checker、未算 Q80 总量，正式信用为0。

本批把第二批 zeroChild 身份扩展到两条 literal parent 的全部 128 个真实 parent/child 配对。`sourceChildD raw c := Int.floor(childDQ raw c)` 只是整数 retrieval：两条闭合有限有理定理逐一覆盖所有 `ChildIndex`，证明 floor cast 精确等于原有 `childDQ`，因此没有引入舍入误差或外供 `hd`。再用第二批 `cast_childDQ` 得到统一 `namedChild_hd b c`，直接绑定实际 `vertexD`。这些有限定理已写为 `by decide`，等待用户编译执行，并非已执行证明 receipt。

所有 child 的正 lower endpoint、真实 closed-child residual≤原始 savedRatio、`2<b≤4` 与真实 closure vertex 范围统一为同一接口。d 保留正负，不声称每个 d 都正；原稿 d≤0时归零的正核步骤交由 upper_jensen 消费。

完整几何连接：两条 raw parent 的 union 精确等于 `Bool×ChildIndex` 的128个半开子盒；同父和跨父均证明无交叠。真实 `rawOwnerDomain` 的 fullCell clipping 保留为64个 childOwnerDomain 的完整 union，原始 signed literal kernel 积分精确分账。固定父 picks 的真实 frozenGap 同样证明 parent 积分等于全部64 child 积分，并用实际 d 给出符号形式的全父 gap 积分下界。没有给任何数值总量。

`batch_target_source_complete=true` 表示本批指定的两父 all64 几何/d/分区源码接口闭合；`task_complete=false` 保留原始 broad target：完整 adopted J5、archive-to-typed loader、全历史family、Q80、clipping reserve、buffered tree、K均未完成。未发现新的原稿数学缺口。

精确导入路径、原始字节哈希和新接口见 REGISTRY.json；接口已发 upper_jensen，供其处理原始 owner clipping reserve 和正核 Jensen。生产源码、旧草稿、Git、看板未改。
