# P1 两侧原始策略的高模数 pre-8 账独审

**T03 新源码通过限定静态审查。** 在真实第四秩前沿上，严格高模数检验的第五、第六单侧事件绝对值账为零，原 rawStopped 与 licensedStopped 的差为零。完整物理差保留原始三个前沿账。源码 `P4AOriginalFull87UnilateralStoppedLevel.lean` 共 18,158 字节，原始 SHA-256 为 `4413db3318142fedbbb7d7817b795863893b42cd981de4d7d77decf66eb31ba7`。

| 源码行 | 核定的实际构造 |
| ---: | --- |
| 36–81 | 负号第五门分别回到原 raw 第五与 licensed 有限第五。后一门按其真实祖先在 cap5 与原 exponent5 间选择。两个门的指数单独得到 ≤299/500，未假定任何策略相等。调用原奇历史立方时，B₅ 的定义已经包含 p₅。 |
| 83–165 | 对原 `stoppedTerminals 8` 的 skip／take 递归归纳，追加的每个素数来自第五后的余表并且 ≤p₅。真实停止深度 <8，所以追加积 ≤p₅²，连空积和偶长都覆盖。对真实终端分别取其符号的原 β±，在系数非零时推得 a<N^ε，因此完整 a·prod(terminal)<N^(3/5)。 |
| 168–230 | 第五双方均准入时，第六查询的符号为正。两个原完整策略各有 `policy_even`，故每个真实第六查询都发出 BOTH，原过滤后的第六列表为空。第五单侧保留原 rawStopped 或负 licensedStopped、原候选之后的余表、质量及出现次数。非零原 stopped 值会给出真实活跃 β 和严格 X<a·prod(terminal)，与上界冲突。 |
| 233–272 | 从原 `sharedRankFour` 成员推出长度 4、正号及 `selectedPrefix.reverse ++ remaining` 为真实递减 roughPrimeUniverse 的子表，因而所需的跨前缀排序、余表排序和各元素正性均由原状态供应。每个事件在其实际质量下为零。原绝对值列表不依赖不同事件的相互抵消。 |
| 274–318 | 原 reduced absolute invoice 的两层清单直接逐项求和为零，原已发表的绝对差不等式给出 stopped 差为零。最后仅从原完整物理不等式删除已经严格核定为零的一项。 |

量词保留原 `delta,n,e,q,om,N,cap,w,z,X,F`。核心条件是原 `data e q om` 的 e 非负、N>1、ε≤1/500、N^(3/5)≤X 与 L=N^ε。零结论适用于原严格高模数测试及相同 F。最后的不等式按原次序保留 `rawOutsideHighQInvoice`、`actualProducerThreeClassLeafBill` 和 `licensedOutsideHighQInvoice`。中间的 ThreeClass 账本身仍聚合三个原类。此处没有给出这些账的数值或渐近上界。

已核对 P1 固定头 `a023ae055d3d90738f6965a2848266aa13089faf` 的两个事件生成器、两侧真实 gate、全部现用账、次序和 parity 的原签名，以及 `c0ee142fe551ea8d36da6bbe6f65a12a0899e490` 的共同上界源。旧 P1 完成的是第六 BOTH 值的消去，本文件才把第五单侧的真实终端逐个支付。锁定 Lean 源的 `Nat.pow_le_pow_right` 也核到要求底数 >0，正是候选提供的条件。边界 ε=1/500 足以消去 X≥N^(3/5) 的严格测试。若另外要求 pre-8 粗小因子合积有固定 θ*<3/5 的幂余量，可先固定 ε<1/500，此时 ε+299/500<3/5。该选择本身没有支付其余前沿。新候选未编译或重放。主要 P1、上界、下界及全局分布节点均无新增 kernel 信用。[锁定 Lean 自然数幂顺序](https://github.com/leanprover/lean4/blob/62eed1db4d67327ec8120be05f1a1b0847d74561/src/Init/Data/Nat/Basic.lean)
