# T07 · 36 行原好双素数的实际普通上筛

在原全部 106 行的有向计数终端中，每个被选 W2 行的四个原正双素数子计数现在已经支付了普通上筛主项。四个窗口共有 36×4 组。两条固定截点和两条移动截点保留原顺序，父词旧因子可以重复。一切结论先选 T，再取偶数 N、原 U3 或 U4、冻结尺度、历史、行、前代和素数对。

记三元组 (b,z,s) 为实际子模 d p q、原截点和原对数参数。Γ5、6 的 z = (Q/d)^(1/s₀)，Γ7、8 的 z = p。有限正量 E⁺ 是原截点的上 Rosser 多项式减去原带接收条件的商素数计数。每个原 W2 行的四项各带 1/5，在原被选位置乘同一标记后求和得到 E_bank。终端为

~~~text
0 ≤ E_bank
Σ_{a,l} m_l · physicalDefect_l + selectedBankRoundingLoss + E_bank
≤ Σ_{a,l} m_l · afterPairs_{a,l} + ε · actualBankTheta .
~~~

afterPairs 在 W1 接前包的 70 行结果。W2 每行保留两个定锚、三个负窗和实际切换余项；四个好双素数项现为原截点的带符号 AP 多项式与原 θ(d p q) H_prev(s) 之和。E_bank 在左侧保留了下一步使用真实前代上界的空间。[全部 106 行端点](Part5OriginalH430BankAfterPairRosser.lean)

## 系数和计数的对应

原好正对同时满足两个实际平方门。其归一化坐标 u、v 满足 1−u−v ≥ 1/5 与 1 < s ≤ 3。原子残余 R = Q/(d p q) = N^{L(1−u−v)}。故 R^(1/3) ≤ z，且 R^(1/3) ≥ N^(η/15)。对固定截点，使用 s = s₀(1−u−v)；对移动截点，使用 s = (1−u−v)/u。R 的正幂下限一致适用于包括深度零、430 代在内的所有原标记位置。闭下端采用原实际素数不与有理壁重合的证明。[原素数对几何](Part5OriginalH430PairPhysicalCubeGeometry.lean)

上 Rosser 的第一处奇前缀检验强制每个活动素因子 h 满足 h³ < R。复用原 ActualRosserCubeReduction，对每个有正负号的测试函数 f，在 z 与 R^(1/3) 的有限加权除数和相等，系数函数本身也相等。原自然水平 floor(R)+1 与 ceil(R) 相等：实际 q∤N，若 R 是整数，冻结 Q 的有理幂表示会推出 q∣N。两侧测试分别取 1/φ(e) 和原 sourceSequenceRemainder(N,b,e)，从而真正的普通主项和原带符号 AP 测试都保持原系数。[逐系数与所有带符号测试的等式](Part5OriginalH430PairExactUpperPolynomial.lean)

原受限计数不超过原无接收条件计数，截点单调性和原有限上筛遂给出 E⁺ ≥ 0。原同 Q 的 JR 主项在 s=3 处等于 1，受限子 θ 由实素数 Mertens 在每窗控制。每窗实对积分的独立上界 45/4 使子 θ 总质量至多 13 个父 θ。报告中使用 13 把每个子主项的统一误差求和，未改变任一原成本、反馈或目标常数。原 H_prev 始终在真实 s 上取值。真实 Γ5–8 好计数也各自满足“实际计数 + E⁺ ≤ 原带符号 AP + θ 乘原二维普通积分 + εθ”。[实际上筛计数](Part5OriginalH430PairOrdinaryCountPayment.lean) · [各原母词的独立积分端点](Part5OriginalH430GoodPairSourcesAtAP.lean)

## 仍开放

四个新签名 AP 多项式仍要由 P3 在原许可标记族上求和支付。E⁺ 是否足够承担 430 代旧 H 的实际增益，需要证明前代源计数。上次 ordinary_rosser 的初始及四轮式还保留 signedPositive；本包的独立好计数端点适用于深度零，但没有在该式中完成原好项与坏 Γ5、Γ9–21 的数额拆分。一般 W2 切换转换价格与全部正素数 PP、原 W1 前代、三负窗和固定锚前代也须支付。整 h34 与 430+11 仍开放。五份源码未做本地 Lean、有限或数值执行，未收到这些字节的远端内核回执。[同批 seed 末端](../ordinary_rosser/REPORT.md) · [字节、来源及完整声明](REGISTRY.json)
