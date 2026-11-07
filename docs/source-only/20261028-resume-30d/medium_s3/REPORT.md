# medium_s3 第四批：actual paperPsi 同剖面 preliminary dispersion

已输出 `Part3MediumActualPsiPreliminaryDispersion.lean`（357 行）及 `Part3MediumReceiverCutoffArithmetic.lean`（161 行），共 518 行。原完整 task_complete=false，local_step_complete=true，batch_target_source_complete=false；未编译、正式信用 0。

已优先修通实际 cutoff 兼容性：原稿明确 Pminus>z，原 CanonicalS2Stages 是 smooth p≤z / rough p>z；旧 canonical receiver 则是 p<c / p≥c。两者在 z 是边界素数时不能直接同名连接。新桥对原 z≥0 定义 strictReceiverCutoff z=floor(z)+1/2，证明对所有自然 p 两种支持谓词精确等价，进而由 prime-power 支持及 small/rough 唯一性证明完整 split 与 labelDW 相等。没有添加 no-boundary-prime 前提，也没有更改任何估计中的原始数值 z。原 inclusive-z retained source 现已在主文件中显式接到该 receiver 下的 actualPsi block source。Poisson 子代理已定向审阅此 161 行桥并按精确 SHA 复用，尚不会将无窗口 Lambda 虚称为单个 trimmed lambda。

源码直接复用实际构造的 paperPsi、实际 paperMWeight 与 qWeight。由原始 q1/beta m carrier 的实区间界证明 psi 在两个原支撑上等于 1，包含闭端点；于是两个正 majorant 可以在实际线性 blockSource 中、Cauchy 前精确插入。之后仅对非负 quadratic 使用正性，把 q/m 扩到 profile 的实际 natural carrier `[Q1/2,5Q1/2]`、`[V/2,5V/2]`。d 仍留在同一 dyadic key 内部。

本稿定义带同一 jointPsi=psi(q/Q1)psi(m/V) 的真实 S1、S2、S3，给出 quadratic=S3-2S2+S1 的有限恒等式。字面 complex paired carriers 使用实际 lambdaTrim、原始 alpha、q*d*r / q*d*s、原始 mean 和 deleted indicator；两份 (r,n1)/(s,n2) 独立，q,d,m 共享。证明三个 literal carrier 和 quadratic cast/real-part 字典，使“同 psi”成为实际公式而不是另一个抽象系数约定。mean 的 (nm,qdr)=1 还被精确分解成 alpha coprime mass 与真实 common-m unit gate。

一般 beta 的实际 L2 乘子全程保留。额外的 betaDivisorL2 推论只使用原始 norm(beta(m))≤tau(m)^B，给出明确有限 sum tau(m)^(2B) 支付；没有假设 beta 一界，也没有把点态 x^epsilon 或未证的渐近普通均值当作对数预算。gamma1 同样保留实际 L2 和。

与 medium_s1 已协调：平滑 q carrier 横跨三个通常 dyadic 片，单个旧 FixedBlock 的 qHi≤2q0 无法容纳整个 `[Q/2,5Q/2]`。S1 子代理复用我的六坐标 atlas，负责三片无交覆盖、FixedBlock literalLambda/common-m count 与 Y/log 预算绑定。此处没有错误地把整个平滑支撑塞入一个旧块。

仍缺 literalS2/S3 与后续 off-diagonal/gcd-clean/restoration/Poisson/CRT carrier 的全部同对象连接、S1 三片 atlas 的末端预算、beta/gamma 普通均值实际量化、trim/exact-product 补项以及 E1/E2/谱返回。完整 medium 和原 S3 目标保持 OPEN。未发现原稿数学缺口。

第三批 source/registry/report 均已按最终 raw SHA 冻结，旧文件未修改。精确导入和 transitive source-only 依赖路径及 SHA 均见 REGISTRY.json。仅做源码与哈希检查，未执行 Lean/lake/checker/额度检查；没有内核验证声明。
