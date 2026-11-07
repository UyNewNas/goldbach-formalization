# medium_s3 第三批：实际 preliminary Cauchy 与 dispersion 求和顺序

已输出 `Part3MediumActualPreliminaryCauchy.lean`，369 行。task_complete=false，local_step_complete=true，batch_target_source_complete=false；全部未编译、正式信用 0。

本稿从实际 `atom.signedError` 出发，首先证明 exact-product 删除及 smooth trim 的精确线性分解。coprime mean 原样保留，分解没有假设 trim 补项或 exact-product 补项已经足够小。retained 线性 source 使用第二批真实的半开 dyadic ownership/canonical choices 全局重索引。

随后对每个真实 dyadic key 进行有限 Fubini：先把原 beta 变量 m 移到外层，再对实际 factor choices 求和得到 `lambdaTrim_d(r)`。原始 gamma2/gamma3、物理 q*d*r、alpha n、beta m 和 deleted congruence/原始 mean 逐项识别，不提供外来的 Lambda 相等前提。

现在一次 Cauchy 应用于整个 `(q,d,m)` outerCarrier，因此所有 d 同处一个 preliminary estimate。内部行平方时保留两份独立 `(r,n1)`、`(s,n2)`；它们共享 q,d,m 的原因是先确定了 outer fibre 后才平方，不是从旧 W 的独立标签中删掉交叉项。源码还证明该实际行的三项 dispersion 恒等式 W-2V+U，U/V 使用同一个原始 coprime mean。

外层一般 Cauchy 保留实际 L2 乘子，不附加一界 beta 前提。仅在显式假设 beta 一界、并满足定理所列 gamma1 一界的特例下，由原始 carrier 推出具体有限 M*Y 量级上界 `(floor(2Q1)+1)*2^(key.d+1)*(floor(2V)+1)`。没有按每个 d 独立调用对数节约界。

需要纠正一个实现顺序理解：若先把所有 q1/d 混入同一行再平方，已形成的 installed W 的两份标签一般不能凭同余条件强设相等。本稿没有作此错误等同，而是证明回到线性 source 后的原稿 preliminary Cauchy 顺序。未发现原稿数学缺口。

仍缺原稿实际正 smooth psi majorant 的 q/m 支持与 domination、preliminary S1/S2/S3 原始 off-diagonal/clean gcd/cutoff dictionary、两个补项的 Shiu/Rankin 预算、后续 literal V/FixedBlock 的全部系数绑定、主项/Gram 估计以及 E1/E2/谱返回。因此本稿不关闭完整 S3 或 medium。原稿 Medium 一般仅要求 |beta(m)|≤tau(m)^B；实际除数矩/L2 支付与 beta 截断、归一化仍待实例化。新源码的 beta 一界特例及其显式 gamma1 一界前提只用于基数/有限 M*Y 乘子推论；精确分解、重索引与保留实际 L2 和的一般 Cauchy 均不需要这些附加前提。

前两批冻结未修改。未运行编译、checker、内核或额度检查；仅进行源码逻辑审阅与依赖哈希读取。准确源与依赖 SHA 见 REGISTRY.json。
