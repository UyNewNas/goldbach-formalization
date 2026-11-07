# lower_chambers 第六批源码交付

四份局部完整 Lean 源码。原完整 task=false，F 完整 dispatched target 尚未闭合，batch_target_complete=false；只标 local_step_complete=true。E 三份 raw SHA 已重核匹配，E/前批 source/report/review 未修改。未编译、formal_credit=0。

本批直接消费独立已冻结 canonical tent producer（SHA 8654416e…），不是新的任意 CandidateBank 参数。其范围是 PairRange [epsilon,59/250]，保留 L6 外部 prime 的真实较大 ceiling；这仍是 tent 子银行，不是完整 W/adopted L5/L6。

`P2OriginalTentSquarePerturbation.lean` 明确支付 selectedWord 的初始和扰动，再支付 remainingWord 的各级 square。总 prefix 最多五项，因此完整与 selected-complement 两组 gate 同时最多上浮 6*step。既不把 selected 初始乘积重置为 0，也不丢原 selected bits。同一扰动引理取 step=0 后公开 `sourceCheck_point_squares_upper` / `sourceCheck_point_squares`，任意 rank 的真实上端 sourceCheck 均推出同 mask/tag 的物理点双组严格 square gates；这只是 downstream 许可传递，不以该前提反向证明 ideal→screen。

`P2OriginalIdealTentCanonicalScreen.lean` 从原 ideal tent 点的独立 strict side margin、full/selected-complement 点门槛与共同 16*step+buffer<margin，推出真实 lowerSide/sourceCheck，再进入该 concrete producer 的 alternatives。没有以 sourceCheck、screened membership 或成功 selector 作为前提。box infimum 的 cap loss<=15*step/2+buffer 与 6*step square loss 同时被支付；较高 tent sibling 不进入 maximization。

`P2OriginalCanonicalTentFrozenChambers.lean` 把 actual codeAt 原 marked prefix 与真实 rational box 接合，给所有 ranks3/4/5 一个统一 mesh budget。第四层对 canonical bank 实际 computed cap3 重测 S3+3t4；第五层读取实际 cap4，保留第四层 inherit，不添加 S4+3t5 门槛。审阅者提醒后，公开端口明确分开 floor:Q（bank 排序 floor）与 root:Real（真实原 L5/L6 物理 root），没有以 rational floor 冒充 piecewise real root。全局 margins/历史 provenance 仍由独立原 source/root supplier 接入。

`P2OriginalCanonicalTentCriticalLicence.lean` 从同一 literal tent cap、mask 和 whole-box slack 推出生产 selected-subproduct critical interval。令 e=4*buffer，精确消费原 moving-residue margin theorem，得到 alpha=1+3*kappa、kappa<=buffer 下的 buffer/2 余量；没有把 critical interval 或 PP 结论改作新假设。完整 prefix sum 仍留在独立 residual query，selected sum 只用于原 selected-subproduct 参数。

仍缺：每个原保留 ideal chamber 的完整 branch/factorization 分类以提供点上两组严格源门槛；原 W 分支和其算术许可；全部 compact child covers、later parent-approximation induction 和 wall payment；真实 L5/L6 root/warm history与本端口的全局采用；full W/adopted bank、非线性 signed count/mean convergence及最终 hLower。F 这些必要引理没有缩小或完成完整 target。

仅静态核原稿、actual defining sources 和 raw hashes；没有 Lean/lake、编译/修复、checker、kernel replay、CI、额度检查或 Git/index/看板修改。精确安装/import map、raw SHA、真前提及剩余义务见 REGISTRY.json。
