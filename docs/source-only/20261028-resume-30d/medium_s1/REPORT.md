# 第四批 medium_s1：实际 owned atlas 与原始 Y 分母

新增三份源码，共 722 行；第三批两份最终 Lean 与 REGISTRY/REPORT 已先按 raw SHA 冻结至 frozen-30c，旧文件未改。全部未编译、未跑 checker，formal_credit=0。

先核对到 medium_s3 第二批已经完成六坐标 (s,t,u,v,d,w) 的半开 dyadic ownership、实际 keyBank 与 canonical 重索引，因此本轮直接复用。新增的 atlasBlock 确实使用第三批实际 preliminary row 的 lambdaTrim；其与 weighted physical ownedSlice 的精确系数等式直接从既有 canonical reindexing 推出。除数界由原 gamma2/gamma3 一界性与真实 divisor injection 推出，非互素 d 系数由 primitive gamma 支撑逐项证明为零。

完整 paperPsi q 自然支撑为 [Q/2,5Q/2]，无法放入一份满足 qHi<=2*q0 的 FixedBlock。本轮构造三个无交自然整数片：[ceil(Q/2),floor Q]、[floor Q+1,floor 2Q]、[floor 2Q+1,floor(5Q/2)]，分别 q0=Q/2,Q,2Q；精确证明唯一覆盖和任意复权重的求和恒等式。d 保留在同一 key 内，只有已证零的 nonprimitive d 被精确删除。原 rough 半开上端点对闭 FixedBlock 额外加入的项，lambdaTrim 也已逐项证明为零。

物理尺度界从原始 admissibility 推出而非作为 cap 假设：occupied key 的 D,R 不超过原物理模数 cap；后者<=4x^2。因而 actual atlas 的 physicalCap<=192x^5、qCap<=3x、roughCap<=8x^2、d-cap<=8x^2。所有 numerator logarithms <= (6+log256)*(1+logx)。

整块 ordinary divisor mean 因此给出 atlasKernelSum<=96*U^2*sourceLog(x)^38/(Q1*D)。同一个 actual paperPsi common-m 绝对常数在所有 atom/key/q片/d 之前选取，再得到

`norm(atlasRemainder) <= C*U^2*(1+logx)^38/Y`, `Y=Q1*2^key.d`。

并已证明 atlasPureS1=atlasMainS1+atlasRemainder，其精确差也满足同界。此处 N=原始 atom.U，幂38固定，未对每个 d 分别调用任意对数精度 remainder。

原稿 rough 是 p>numeric z。旧 strict-small receiver 的参数须取 strictReceiverCutoff(z)=floor(z)+1/2；本轮通过 originalNumericAtlasRemainder 明确调用已冻结的 medium_s3 算术桥。未在估计里更换原始 numeric z，也不使用 no-boundary-prime 假设。FixedBlock 的频率字段对 pre-Poisson S1 完全不使用，构造中取 inert positive singleton；不声称它已经标识 E3 的真实频率载体。

原完整任务仍未完：尚需把 medium_s3 的 samePsiS1_cast_eq_literal 全部 carrier/Fubini 操作接成 atlasPureS1 的一个整体精确等式，包含 m common-count 求和、三q片、nonprimitive d 零项和 rough 闭端零项的合并。这里没有把该等式作为前提，也没有把已得 atlas budget 直接叫作原稿完整 S1 验证。S2/S3、principal cancellation 与最终 medium 仍 OPEN。local_step_complete=true，batch_target_source_complete=false，task_complete=false。

精确导入路径/raw SHA、当前生产路径 SOURCEONLY 依赖的范围和剩余义务均见 REGISTRY.json。
