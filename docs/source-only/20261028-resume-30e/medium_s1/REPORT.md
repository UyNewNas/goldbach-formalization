# 第五批 medium_s1：原始 S1 实际总等式与 key/margin 支付

交付四份 Lean，共 828 行；第四批三份最终 Lean、REGISTRY、REPORT 已先按 raw SHA 精确冻结，旧批次未改。未运行编译、Lean、lake、checker 或额度检查，正式信用为 0。

本轮首先从 medium_s3 已独立定义的真实 principalRow 和 samePsiS1 出发，而非再次定义 atlas 自恒等式。由原 (nm,ell*r)=1 门把 n 均值分解成实际 alphaCoprime，再证明两份门共享同一个 m，其合取恰为 (m,ell*r*s)=1。完整有限 Fubini 后原 S1 逐项变为 paperCommonMCount；原 gamma2/gamma3、alpha、q/d/r/s、q/m paperPsi 和 h0 质量均保留。随后实际三q片、gamma强制为零的inactive d与rough闭端零项接成 original_samePsiS1_eq_owned_atlas，总等式的两端在前批已独立定义。

第五批实际源在 Cauchy 前保留了 primitive (q,a)=1 门。因此另行消费 medium_s3 冻结的 PrimitivePsiSource 与 LiteralS3Stages.primitiveS1，并给显式过滤版 atlas/Main/Remainder。过滤版误差不能由未过滤误差的范数控制；本稿在每个真实 singleton-q FixedBlock 上复用统一 count，再只扩大正除数 kernel。由此 original_primitiveS1_eq_main_add_remainder 与 original_primitiveS1_sub_main_le_log_over_Y 直接适用于后续 primitive S2/S3 的同一源；没有混同两支 S1。

实际 keyBank 是既有六坐标 owner 的有限像。由原 physicalCap<=4x^2 和 2^log2(cap)<=cap 导出其真实基数 <=常数*(1+logx)^6，而非把log重数作为前提。先保留每个真实 Y_k=Q1*D_k，证明全部key的 ΣY_k*|S1_k−MT_k|<=C*U^2*(1+logx)^44；再把原 outer finite Cauchy 的额外实际 keyBank.card 因子也计入，得到固定 log^50 预算。

原 strict restricted-medium monomial已提供 U<=x^(1/2)，结合x=U*M得到真正的 M>=x^(1/2)。复用既有 Mathlib-backed log/power极限后，统一阈值先于atom、receiver/trim及全部key，可将上述log44和log50总误差支付到 M*U^2/log(x)^A，任意 A。原 numeric z 只经已证 strictReceiverCutoff 离散支持翻译，不在分析估计中更换z。

本批目标的源码衔接已写完：batch_target_source_complete=true、local_step_complete=true；原广义 task_complete=false。完整 medium、S2/S3主项取消、E1/E2、谱返回和主定理仍 OPEN。beta L2及后续固定log因素仍须在完整Cauchy链中按相同精度选择接入；本次all-A总余项定理可供该步骤消费。没有假设 principal Gram 的目标上界，也未把原稿内部结论改成 primitive。

精确源、模块安装映射、peer无环依赖和所有 raw SHA 在 REGISTRY.json。源码数学/接口审阅与编译/内核验收严格分开；本轮 compiled=false、formal_credit=0。
