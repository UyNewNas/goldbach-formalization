# coefficient_signed 第五批：完整同系数 inner/wall 重构与全部 marked/beta 质量核算

本批输出两份 Lean，421 行、17 条新引理。`task_complete=false`、`local_step_complete=true`、`batch_target_source_complete=false`；未编译、正式信用为 0。第四批最终三文件 raw SHA 已匹配并冻结，未改动。

`P5All16ActualInnerWallReconstruction` 以真实 PairMark=Σ all16 ordinary t,(small e,retained rough d) 为独立载体。它包含 W、原 marked 前缀、small-beta 的全部和及显示的零行。先用原 joint_modulus_injective，再用 small/rough 分解唯一性，证明完整 q=fullPrefix(t)*(e*d) 对全部真实 PairMark 的注入性。没有把“aggregate coefficient 一界”当新假设，也没有停在固定 prefix/e 的唯一性。

wallRho 独立定义为 actual wallPairs 的完整 q 纤维和，保留真实 rowCoefficient 的符号和 beta。wallPairs 是 canonical residual log 点不落任何 certified inner cell 的真实补集；每个这样的点由第四批覆盖证明仍有 proper affine row 的 wallReserve 见证。原算术边界点未删除。证明 wallRho 在其真支持上等于唯一真实行、off-support 为零、全 q 一界；其支持仍在原 jointSupport。

`actual_all16_inner_plus_wall` 对任意 signed F 精确证明完整原 jointPresievedSigma 和等于 inner fine-cell restrictions 加独立 arithmetic wall pushforward。每个点最多一个半开 inner cell，因此没有重复计数。F 可以直接取 count-minus-exact-coprime-mean；同一 coefficient 和同一完整 q 始终贯穿。外绝对值界 `actual_wall_test_abs_le` 只把真正 wallSupport 上的完整核 sum |F(q)| 留给算术支付，未假设或声称它已是小量。

`P5All16CompleteMarkedBetaMass` 进一步证明 PairMark 全 q image 恰为 jointSupport、全部 marked 与 small-beta 的绝对 coefficient mass 正好等于 sum_q |jointPresievedSigma(q)|。wallRho=原 joint rho 乘实际 wall mask 是由两边独立定义和唯一性推出的。使用原真实 common-beta 参数和 arithmetic support，完整质量有 floor(N^(153/256))+1 的模数域界。这里确实包含了所有 marked/e 和，但**这是模数域绝对质量，不是独立于 N 的 restoring tensor-scalar budget**。

完整第五批仍未闭合：innerAtomLinear 目前是实际 row weights 的细网格限制，尚未证明其就是全部 marked common-fine Cartesian gamma atoms；它不能被定义替换为候选张量以冒充证明。coefficient_bv 正在独立导出 compact W4 的 gamma3*beta 一界与 true whole-box tensor 接口；该 policy 与本 NEW all16 common-beta sigma 不自动相同。完整 source/atom matching、marked/common-fine scalar 总质量、wall 算术小量及最终 PP 仍需证明。本报告没有把 fixed-prefix/e 预算、单 q 一界或模数数量界改名为完整 fixed tensor-scalar 预算。

已把冻结 wall 源及精确 SHA 提供给 coefficient_rough、transfer_trace，供其在原实际 full-q 核上做真正总质量支付；pp_fourier 的旧 native sigma tail 独立推进，未与 NEW common-beta sigma 混同。未导入尚未冻结的 peer 文件，也没有以 peer 的最终预算结论作前提。

本次未发现新的原稿数学缺口；剩余为严格对象绑定、共同 alphabet tensor 重构及算术支付的实现义务。仅做作者静态证明审阅、token 检索和 raw SHA256 固定；未运行 Lean、lake、checker、数值 replay 或额度检查。依赖路径、import 安装顺序、namespace、声明、原稿 anchors 与 raw SHA 均在 REGISTRY。
