# coefficient_signed 第三批：真实 sorted block/atom scalar 衔接

已交付 `P5All16SortedBlockAtomScalar.lean`（407 行，18 条新引理），以及本登记与报告。`task_complete=false` 保留原始完整目标；本批有限两标签 sorted-block 衔接为 `local_step_complete=true`、`batch_target_source_complete=true`。未编译，正式信用为 0；前两批文件未修改。

本批不要求调用者提供 sorted block decomposition、同系数等式或 chart coverage。对真实 retained rough `d` 计算 canonicalFineWord 和 run-length blocks，再以这些实际 keys 对 retained 和求纤维。对于任意 block-box product，实际槽列表提供素数分解；squarefree 与原始 upper gate 通过第二批反向覆盖给出 genuine retained `d`。由唯一素因子分解，任意 box tuple 与 canonicalSlots 互为 permutation；map 到实际 half-open owners 后，原 key word 与 canonical word 互为 permutation，二者弱序使它们逐项相等，故其 blocks 确是该原 key。这证明真实 key fibre 正好等于整个 Cartesian atom 中通过 squarefree 和原始 gate 的产品集，双向包含均在代码内。

复用现有 generic disjoint prime-label normalization，实际 twoFineBox 的 prime/disjoint 性由原始几何 owner 直接证明。每个 block 的 `M_res` 是 label occurrence counts 的 factorial product；归一化卷积在所有整数上一界，包含重复素数产品。对 retained squarefree `d`，原 raw owner orders 的 `(M_res/k!)*(T_J/M_res)` 全和严格等于 sorted block 的 `T_block/M_block`，二者各自由真实 Cartesian fibre 归一化等于 1，因此没有假设一个新的 multinomial scalar。

`blockAtomLinear` 是完整 Cartesian atom 上的原始有符号和，其外标量精确为 `rawBeta_k(e)/M_res`；只对 rough product `d` 取 `mu(d)`，原 upper gate 保留在 full-product test 内。重复素数词在取绝对值前因 literal Mobius 为零。marked 前缀不进入这个 factorial，测试词 `u` 不与 marked `t` 混同。按真实 all16 marked family（包含 W 和零行）、small `e` 和 sorted block keys 求和，得到任意 signed F 的原物理 `jointPresievedSigma` 等式，并给出逐点 `all16BlockSigma=jointPresievedSigma`、count-minus-exact-coprime-mean 等式及第二批全 k squarefree raw 的合成。完整测试模数始终是 `fullPrefix(t)*(e*d)`。

边界：这些是实际 coarse 两标签的精确代数原子，原 coupled upper gate 仍留在 atom test 中；尚未证明所有 atom 对 analytic 分配的 gate-uniform 许可。任意更细 alphabet、同盒三组分配、scalar 总绝对质量预算、unrestricted repeated-rough 在 count/mean 两边的绝对误差包络，以及最终 PP 渐近估计仍需推进。因此不计完整 coefficient_signed 或主定理闭合，也不等同旧 all-prime native sigma 与 common-beta 系数。

本次未发现新的原稿数学缺口。已做作者静态证明审阅、精确 SHA256 固定及禁止占位证明 token 检索；未执行 Lean、lake、checker、数值 replay 或额度检查。全部直接及关键传递依赖的源码路径、声明、namespace、import 安装映射记录于 REGISTRY，供独立 reviewer 与编译专员使用。
