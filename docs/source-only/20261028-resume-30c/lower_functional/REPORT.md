# lower_functional 第三批源码交付

新增 `P2N48OriginalQ80DirectedRowSoundness.lean`，328 行，未编译、未执行任何 finite/large checker、零正式信用。前两批和全部旧草稿均冻结未改。

本轮首先将第二批真实 archive decoder 的 term=1、iw≤iz≤iy 接到已有 Phase11 四种 tied-simplex 实际体积定理，推出每条 `actualRetainedRows` 的 `massLower ≤ parentUnweightedMass`。第一批/第二批消费者的这个 hMassLower 输入因此由实际行和几何证明供应，不再外加。

对照原始 `I` 类和 n48 producer，新增符号有向算术 soundness。证明 signed integer floor/ceil 与 Python //、ceildiv 一致；证明四角积 min/max 在非负区间确实选择 lo*lo 和 hi*hi；然后保留原始两条乘法链：baseline 为 `floor(lo(K*C)*massLo/Q)`，omega cost 为 `ceil(ceil(hi(K)*omegaHi/Q)*massHi/Q)`。在实际有序质量 Z 的区间和实际 Buchstab query 上界下，源码推导真实 baseline 下界及真实 switched cost 上界，没有把这两个整体积分不等式直接当输入。

还核对并修正一处旧 receiver 过强条件：Phase5 的 unclamped integer predicate 不是 literal producer/replay。原始两者都保存 `max(0,baselineLo-costHi)`；若 stored floor=0 而有向舍入差为负，旧强谓词会拒绝。新 `rowPayloadCheck` 保留 max，零floor分支用真实 omega≤C cap 证明真实saving非负。旧 implication 本身仍是充分条件；这不是原稿缺口。

`DirectedPayload` 只定义未来证书的接口，并检查其 originalOrdinal/key 与同一 SourceRow 相等；没有伪造或生成任何实际 endpoint 数值。当前七列 archive 只有 stored floor，没有 massLo/massHi/omegaHi 全端点。因此仍明确保留内部义务：从 original block_mass/ordered_weights 及定向log算术导出真实Z enclosure、从真实Buchstab网格/范围导出omega query上界与cap、绑定实际payload并执行逐行finite检查。它们不是可推迟的外部经典定理，也不是已完成工作。

最终消费者已把这个 soundness 接回同一 actualSelectedCoefficient 的 rows+uncoveredCost 分解，原有 hMassLower 和 hkeys 已由真实前驱供应，未覆盖完整负域的 remainder 仍保留。`local_step_complete=true` 仅指上述必要符号步骤源码闭合；`batch_target_source_complete=false`、原完整 `task_complete=false`。没有声称实际数值PASS、内核通过或新原稿数学缺口。

精确源码、前驱和原始算法SHA见 REGISTRY。
