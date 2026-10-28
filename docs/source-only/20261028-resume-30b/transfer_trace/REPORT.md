# transfer_trace 第二批

新增 `P2RoundedU6NativeJointLedger.lean`，325 行；完整局部文本，未编译、零正式信用。第一批文件冻结未改。

第一批把实际 finite-cell rounded rho 接到原始 prime source，旧 `P5JointNativeSignedRegroup.LowerData` 却固定使用 raw lower rho，不能容纳 mesh 舍入。本批新增 `RoundedLowerData`，保留每个真实 U6 pair 的 policy、w、L、mesh，直接由 compiler 的点态 minorant 推原始 quotient source 的有限下界，并在相同 E 的第六项上求和。没有假设 coefficient equality 或所需 U6 mean。

随后把这个实际 rounded U6 与既有 FULL16 native U10/U11 在物理模数 fibre 内相减；正负侧共享同一模数时先抵消，再允许后续取范数。U10 的低第四素数段保持 unmasked；U11 高段仍用原 last-pair E 的补集，H 等号留高侧、D 上端仍完整。原 native fallback count 原样保留。

最终 `original_eleven_term_rounded_same_sigma` 把这条实际 `+U6-U10-U11` 接到原稿十一项 paired-prime ledger。count、exact coprime mean、primitive signed error 与 centre-prime correction 共用同一 sigma；若改用 total prime mass，则明确减去带符号 modulus-prime correction。不要求聚合后的 sigma 非负或绝对值≤1。

这闭合的是有限 count/mean 衔接。完整任务仍开放：实际选定 CapPlan/branch licence、舍入损失趋零、same-sigma 支撑指数和 signed PP、数值 mean/fallback 及其余 Chen 项尚未闭合。未发现新原稿数学缺口。所有依赖和SHA记录在REGISTRY；source-only第一批导入的安装路径已明确。
