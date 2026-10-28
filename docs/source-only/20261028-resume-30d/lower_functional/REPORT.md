# lower_functional 第四批源码交付

新增 `P2N48OriginalStrictLogMassAndOmegaPorts.lean`，370 行。未编译、未执行任何行/证书/大checker，正式信用为0。第三批及此前文件冻结未改。

本轮完成两条实质连接。第一条是原始 n48 高带严格bin分支：由 literal intervals 和实际物理端点证明 `fullParent=nativeBox`，再对真正四维 Lebesgue 积分使用 Fubini，并对指定 z 坐标的 `1/z²` 直接做FTC，得到

`Z = log(tHi/tLo)*log(uHi/uLo)*(1/zLo-1/zHi)*log(wHi/wLo)`。

这是原 `ordered_weights/block_mass` 的严格分支真实 log-moment 公式，保留额外的1/z，未以普通体积代理加权质量。随后复用既有 `P2DirectedLogRounding.Expr.enclosure_sound` 和三个原 scalar `RationalLogCertificate`，再用有限 rational containment 检查连接到同一 actual payload 的 massLo/massHi。终端真实 Z-enclosure 不再作为调用前提。Expr 是相同精确数学公式的有向包络表达式，没有宣称其指令与历史 Python I 输出字节一致；actual payload containment 仍须正式 finite check。

第二条对全部高带行（含三种tie）成立：原始未截断 `rawQueryLower/Upper` 包含真实 Buchstab argument。复用已有原始多项式/Bernstein `OmegaCoverCertificate.check_sound`，有限cover与numerator比较分别供应 payload omegaHi 和准确 omegaCap。这里没有另造Buchstab节点推导，也没有把 hOmega/hCap 实函数目标当输入。

最终源码将这些接口接回第三批，给出 actual strict row 的 hBaseline/hOmegaCost ports、原Q80 saved bound及同adopted-mask实际sixteen-policy cost recost。输入仅剩精确source row、严格branch、scalar log证书/finite containment、原Omega有限cover/整数比较及原rowPayloadCheck。所有数据checks都是源码中的前提接口，没有运行或声称成功。

完整目标继续OPEN。zwTie、uzTie、uzwTie 的真实加权moment仍需按原r,s signed alternating formula证明Fubini与log-moment，不能借普通体积的1/m!跳过。actual log证书、directed payload、Omega covers与完整uncoveredCost/priority域认证仍缺。`local_step_complete=true` 指上述严格分支和全高带query衔接的源码闭合；`batch_target_source_complete=false`、`task_complete=false`。未发现新原稿数学缺口。

本轮还只读核对了仓库固定mathlib提交的 [Fubini主依赖](https://raw.githubusercontent.com/leanprover-community/mathlib4/e4c91783ca8e6a7c693ae624ade32fd22d4e43c1/Mathlib/MeasureTheory/Integral/Pi.lean)，没有运行编译器。精确本地原始SHA见REGISTRY。
