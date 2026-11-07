# 第五批 certificate_enhanced

本批新增两份源码，推进真实同 Q 计数层。完整 H248 增强归纳继续开放，`task_complete=false`、`batch_target_source_complete=false`；本批已写的窄步记 `local_step_complete=true`。全部源码未编译，正式信用为 0。

`P2EnhancedActualBuchstabTransfer` 直接消费实际 `source_buchstab_selected_modulus`，把原来的 convolution 权推广到给定有限 sigma。所得等式是原 Phi 的真实计数分解；每个 child 使用同一 Q、原窗口的 `[low,high)` 端点及证明合法的 `(d*q)*N` mask。实际窗口给出 `d*q^2<Q`，继承参数为 `log(Q/(d*q))/log(q)`，严格保留两端 `s-1<argument<=t-1`。确定的 `floor(Q/(d*q))+1` Rosser level 及每个实际非零系数的完整 `d*q*r<=Q`/coprime support 均从该几何推出。

相同模块在真实 divisible prime sequence 上独立定义 `childPolynomial`，再由既有 density identity 拆成相同系数的 li/phi AP 模型与 signed remainder。这里 li/phi 是 AP 模型，有限 exact-coprime population 不是本声明的含义。真实 finite lower/upper Rosser inequalities 给出 child sandwich，进而给出 Phi 的上下 Buchstab transfer 和原正 Theta 下的 gain 归一化。没有抹掉 signed remainder，没有为 H248 定义 ordinary-rho density。

`P2EnhancedActualTwentyOneNormalization` 消费 lower_tail 本批独立的 `actual_sameQ_signed_child_correction`。其 `/5` receiver 使用原 positive Theta、原三个 negative-child AP 模型及 signed remainder；原两项 positive pair 与全部 marked switched counts 以真实计数留在右边，系数均为五分之一。参数仍是原第二种子 tuple `(11/5,227/50,353/100,29/10,61/25)`，没有推广为已许可的36个 bank action。统一 threshold 先于 N/Q/D/sigma 选择。没有引入 K、H/h endpoint、BankEndpointLicences、最终 child mean 或 generic Sound 前提。

外库的实际读取位置为 WSL `/home/slava/codex-lean-ve/native-packages/goldbach/research/wu2008/src/MathlibNt/Wu2008DoubleSieve/`。`PhiBuchstab.lean` raw SHA 为 `b1bdd41db5d848b87050f0f1f801b6ee49b0e32ce8e5bed38cb3153526267833`；`RosserSieveConsumer.lean` 为 `299d9463ddcf293fde2a8286fad90160084f4d465a21908081c8f724e68339dc`。REGISTRY 给出 SourceCarriers/SignedSieveRemainder、生产 Phi/Theta 定义、peer 源码及 D 冻结的实际路径和 raw SHA。Windows worktree 中不存在的 `.lake/packages/goldbach/MathlibNt` 不作为已读取路径。

剩余连接是实质的：同一实际 marked family 的递归 admission、full/selected squares、alpha 与 stable cap/fibre transport；有限 signed child sums 到手稿普通正积分的统一解析逼近；真实 selected W1/W2 switched prime-product family 的 positive-K/PP 许可；frozen184 seed、前184代及每个 intermediate upper invariant；以及原70 W1/36 W2 immutable-old actions 的完整计数归纳。此处的普通 Rosser child polynomial 与 lower_tail 的三负 child 系数分别由各自真实 source 定义，没有被互认成同一个 enhanced coefficient。没有用有限整数和替代手稿 integral，没有运行 checker、数值重放或编译，也未建立新的原稿数学反例。

安装图只是一份交付说明：两份本目录 Lean 分别对应 `ImbalancedChen/P2EnhancedActualBuchstabTransfer.lean` 与 `ImbalancedChen/P2EnhancedActualTwentyOneNormalization.lean`；后一文件另需独立安装 lower_tail 的两份 E 模块。没有写生产树。所有前批源码及元数据保持原字节冻结。
