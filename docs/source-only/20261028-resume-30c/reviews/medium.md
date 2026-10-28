# 第三批 medium 五项独立源码审阅

五项均为 **SOURCE_REVIEW_PASS**，限最终七份 Lean 的数学逻辑、原稿范围、循环前提及精确依赖。共 2639 行；57 条登记/冻结 path-SHA 配对全吻合，另核一条本目录 import hash 别名。未编译、修编译、运行 checker、安装或查额度；`kernel_verified=false`、`formal_credit=0`。五项原完整 `task_complete=false`；完整 medium 和主定理继续 **OPEN**。

| 任务 | 实际推进 | 保留边界 |
| --- | --- | --- |
| medium_s1 | actual paperPsi 的零模质量、统一 progression O(1)、Mobius coprime Cτ；新 same-psi MT+error 接 literal 固定块正核 | 全局 common-q/d atlas、lambdaTrim/lambdaAt 绑定、Y=QD 与完整 d-block 渐近 |
| medium_s2 | q/m 确用同 paperPsi；full/kept/三尾与实际 paperBlock 重排；真实 product interval、signed reduced residue、原始 Shiu 四窗口及显式 90·V/l·τ(l)^5 对数预算 | same-psi collapsed-filter、真实全 dyadic/mixed-block 覆盖和 (8) 最终尾求和 |
| medium_s3 | 从真实线性 signedError delete/trim/exact 分解，经实际 owner 重排，在全部 (q,d,m) 上一次 Cauchy后才平方；同 mean 的 W−2V+U | 实际除数有界 β 的 L2 支付、paperPsi 插入、后续 literal S1/S2/S3 与错误项 |
| medium_variance | 固定真实 r*k 序列后调用 native primitive 大筛；完整有限 high conductor/quotient 和；low+high=actual variance | 固定对数/尺度吸收、粗方差与加权 (14)、positive Gram (15)、四 chart 返回 |
| medium_poisson | actual D-window 的全 gcd/quotient 重索引；真实 lcm/CRT residue 保留；显式 clean 分支严格证明式 (21) | 全局 clean/nonclean、physical gcd D 到 smooth d/FixedBlock/E3、enlarged q、全 l₁/Abel/谱返回 |

S1/S2 的旧 m cutoff 不再被重命名：新同 ψ 计数和包都显式使用已构造 paperPsi。S2 的原 primitive 只提供自然 X,H,q,b Shiu 接口，A/X0 先于所有变化参数；四个真实窗口和 moving reduced class 逐项证明满足条件。最终从 l≤x^(4/5)、x>3^9、x≥3X0 推出原 primitive 门，没有把所需 Tψ/S2 结论当作前提。

S3 的共同 q/d 是在线性源外层 Cauchy 后生成的；没有从旧平方 W 删除交叉项。一般 Cauchy 保留实际 L2 乘子；有限 card/MY 推论另外假设 β 一界。原稿只保证 |β(m)|≤τ(m)^B，该特例不能代替原始 β 的除数矩支付。作者已仅修正这点措辞与 prior held 依赖 state，Lean 未变。

Variance 以同一个实际 r*k mask 跨 f 大筛，primitive cell 为 K·N·(D+N/D)，完整高项为 K·N·(Q+N/R)·(log2 Q+1)·(1+log Q)^2。额外固定对数明确留下，未以 Q^ε 吞掉任意对数节约。

Poisson 的 D 是物理尾积 gcd，尚未识别为 preliminary common smooth d。gcd/quotient 恒等式保留全部 D 分支；式 (21) 仍需 A.Coprime(w₂) 与 N₁.Coprime(N₂) 等 clean 门。outerGate 和内层 unit mask 不保证这些门，例如 p=2,r=1,w=2,D=1,N₁=N₂=t=1 时 A=w₂=2。故全 general-D/root 分支必须保留；这不是原稿缺陷的证明。

未发现目标结论当新前提或具体数学反例。具名原始 Shiu、大筛、Mertens primitive 的基础证明保持既定递延边界；本轮没有声称完整传递导入/公理闭包或外部 API 的内核验收。精确最终源、registry、REPORT、必要前驱及逐条 hash 见 `medium.json`。
