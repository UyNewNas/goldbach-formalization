# 第三批 medium_poisson

新增 Part3OriginalGevreyCleanE2Quotient.lean，原目标 task_complete=false；local_step_complete=true；batch_target_source_complete=false；未编译，正式信用 0。前两批冻结，生产文件未改。

从实际物理配对行出发：令 D=gcd(r*s,rprime*sprime)、delta=gcd(r,D)、q=D/delta、t=s/q，w1=(r/delta)*t，w2=(rprime*sprime)/D。直接复用生产 GeneralDGateNormalization.sum_gate_reindex 与 normalized_lcm 的任意载荷精确 bijection，载荷取当前 actual paperPsiNonzeroMode 和真实 D-window，保留 actualPsiQWeight、gamma、原始 alpha 与全部共轭。exact_gcd_partition 的有限 image ownership 没有猜测 D 的独立大盒；fullOriginalRow_eq_quotient_rows 已把真实随 D 变化的 Fourier 窗口一同分组和重索引。

这个载荷与第二批 rowRetained 在相同 gcd 分支上严格相等。因此原 time-domain majorant 始终是第二批 paperMWeight=paperPsi(m/V)；没有把旧 bump 或额外 low-pass 塞进新载荷。完整物理 L 精确变成 (p*D)*w1*w2。

式(21)从三个真实逆元的整数整除关系证明。u=inv(N1*w2,A)、v=inv(N2*A,w2)、tInv=inv(N2*A,N1*w2)，A=p*D*w1；归一化分子同时被 A 与 N1*w2 整除，clean 互素条件允许合并。实际 constructed CRT residue 先证明等于这两个逆相位，再得到原稿的 difference reciprocal × retained slow phase；没有把相位恒等式或 E2 输出作为前提，任意整数 a,h 均保留。

边界必须保持：outerGate 与 t unit mask 不推出所有 clean 条件。例如 p=2,r=1,w=2,D=1,N1=N2=t=1 时 outerGate 成立，但 A=2,w2=2 共享因子。新文件只对显式 clean 子分支推出逆元许可证；其余必须保留原 general-D/root packet，不能据此丢弃。这是实现域区分，原稿已有 coprime partition 的证明责任，未发现原稿数学缺口。

尚待完整外层 family 到命名 E2/FixedBlock/E3 及实际矩形的重索引、全局 clean/nonclean 分支与 alpha gcd/support 的绑定、扩大的正 q-majorant 支撑、完整系数预算与 Abel/谱返回。没有把这个局部 quotient/phase 字典误称完整 medium。

静态检查只覆盖单文件注释闭合、无占位符和固定 SHA；未执行 Lean/lake/数值 checker，未检查额度。具体引用路径、哈希及新增声明见 REGISTRY.json。
