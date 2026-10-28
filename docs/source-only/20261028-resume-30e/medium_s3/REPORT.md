# medium_s3 E：真实 primitive-q S3、单零恢复与 Poisson 源

三份完整局部源码，共 667 行。原完整 task_complete=false，local_step_complete=true，batch_target_source_complete=false；全部未编译、正式信用 0。D 批两份 Lean、REGISTRY、REPORT 已按最终 raw SHA 复核冻结，未修改。

`Part3MediumPrimitivePsiSource.lean` 先修通实际 primitive q 入口。D 未滤 q 的 smooth quadratic 是合法正性上界，但不能直接当作 primitive CRT/Shiu 载体。E 从原始 gamma1 support 门证明非 primitive 原 q 在线性源贡献为零，再对保留 primitive 门的 `(q,d,m)` 一次 Cauchy，之后只扩到 `paperPsiNaturalCarrier Q1` 的 primitive q 子集。真实 beta L2 全程保留。实际非零 lambdaTrim 的 `(d*r,a)=1` 由 actual choices 中 gamma2/gamma3 的原 physical gates 逐项证明，未把全部 dCarrier 声称为 primitive。

`Part3MediumLiteralS3Stages.lean` 给该 filtered primitive-q 同载体的 S1/S2/S3、字面 complex pair term 和同均值 dispersion identity。两份 rough/alpha 标签独立，q,d,m 共享。S3 明确分为 diagonal 与 off-diagonal。仅在真实 off-diagonal、同一个正 m 上复用既有 single-zero arithmetic，证明恢复为 deleted 加两项单零；double-zero 在此才被排除。最终 S1-2Re(S2)+S3 的记账仍保留 diagonal、两项 single-zero corrections，没有把零频或 principal variance 宣称取消。

`Part3MediumGenuinePoissonFibre.lean` 从实际 restored S3 m 和原 paperMWeight 证明 productProgressionWeight 的真正源恒等式。非零实际 lambda 推出两个完整物理模数的 primitive residue 门；零 lambda fibre 逐项为零。然后调用已有 constructed CRT 和实际 paperPsi finite-residue Poisson theorem，完整保留 physical lcm、构造 residue、zero mode、两向 signed Fourier modes、任意 caller H(v) 和真实 finitePacketError。最后给出 paired carrier 与 fibre+m 的独立显式双射，证明实际 off-diagonal restored 总源等于该真实 Fourier packet 总源。未把 peer family/SourceBind 或 Poisson 目标作为前提。

原稿数值 z 与旧 strict receiver 的转换继续严格使用冻结 D 的 receiver=floor(z)+1/2 接口；本 E 的 lambdaTrim 参数是 receiver，不把 original numerical z 偷换。三组 peer 已获得独立 constructor/term/载体接口：S1 负责 filtered atlas/common-m 和误差预算，S2 负责原 single-congruence/gate/cutoff 字典及尾界，Poisson 负责 genuine family/clean E3/H(v) 衔接。这里不反向导入他们的 E 结论。

仍未完成 coefficient/shift-divisor、gcd clean、close-pair 等删去项的定量支付，未界定 diagonal 与两项单零的原 Rcal*(N+Y) 预算，也未闭合零频 MT+P 的正 Gram 方差比较、物理 H/family、E1/E2 或谱返回。因此完整 medium/S3 保持 OPEN。未发现原稿数学缺口；本批识别并修正的是 D 与 primitive CRT/Shiu 的接口范围。

准确源码、逐项直接导入、既有 primitive 源和冻结前批 raw SHA 见 REGISTRY.json。仅检查源码与哈希，未运行编译、内核、checker 或额度检查。
