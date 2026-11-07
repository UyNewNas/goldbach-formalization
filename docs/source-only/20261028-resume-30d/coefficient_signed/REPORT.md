# coefficient_signed 第四批：实际细网格、整盒门与残余标量预算

输出 `P5All16FineMeshGateScalar.lean`（318 行、15 条新引理），REGISTRY 与报告。第三批三文件的原始 SHA 已重新核对并冻结，未改动。`task_complete=false`；窄步骤 `local_step_complete=true`，本批完整目标 `batch_target_source_complete=false`。未编译、正式信用 0。

新细网格的字母表不是替代素数范围：已证明它恰为原 `actualPrimeFineLabelFinset` 在 tau=1/(m+1) 时与真实 physical roughPrimeFinset 的交集。原始 p 不整除 N、rough lower cutoff、Z ceiling、cap 和半开端点全部保留。真正 inner cell 的整个实际 Cartesian prime box 中，每个 tuple 都通过原始 upper-prefix 与顺序门；该结论由原 log 区域及 fine prime dictionary 推出，没有要求调用者给 gate-uniform 结论。

每个真实 retained rough divisor 的 canonical word 先被放到原始 N-scale 的 [0,1) log box，再以既有 mesh wall 定理得到一整个合法 inner cell，或一个明确 proper affine row 的 wallReserve。crossing/边界素数仍保留在 reserve；未用连续零测删除算术点。`actual_all16_sigma_mesh_or_wall` 从真正非零的 all16 jointPresievedSigma 提取同一个 marked q=fullPrefix(t)*(e*d)、真实 small e、原始 residual d、固定 rank 界及该 fine cell/wall 见证，包含 W。

整盒分组直接调用原 frozen selected-pair 算法：高秩前三个原槽及 tail 的 upper endpoints 先计算一次，之后整个 Cartesian box 使用同一 occurrence lists。已证明原列表 permutation、exact raw triple tuple sum，以及三组所有 tuple 的原始 endpoint product bounds。低秩留在第一组，交由独立 BV 路径；代码未把 raw partition 冒充解析容量许可。

标量保持原 beta_r(e)/M_res，M_res 为 mesh 标签 occurrence counts 的 factorial product，未加入 marked factorial 或新的 group factorial。从真实 beta 的一界与 M_res>=1，得到每个残余 cell 的 absolute scalar<=1，以及固定 prefix、固定 small e 时所有 r<=R 的残余 scalar mass<=sum_(r<=R)(m+1)^r。该预算与 N、marked prefix、small e、beta level 和测试函数均无关，但**没有对这些 prefix/e 求和**，故不能当完整 marked/raw coefficient 的 scalar mass 定理。

仍须推进：真实完整 signed coefficient 的 inner atom+arithmetic wall-error 求和恒等式、wall/face 统一算术支付、marked common alphabet 与 beta 的完整三组归一化、真实 all16（含 W）容量和 medium monomial licences、完整 scalar mass，以及 collision 与 PP。当前只能给实际 support 与固定 residual atom 的窄预算，不能据此宣称第四批完整目标闭合。

本次未发现新的原稿数学缺口。仅做作者静态源码/数学审阅、禁止占位 token 检索和 raw SHA256 固定；未运行 Lean、lake、checker、数值 replay 或额度检查。原稿正文与 Appendix coefficient 模块、所有直接及关键传递依赖的路径/namespace/声明/哈希见 REGISTRY。
