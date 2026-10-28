# medium_s3 F：实际 CRT 零模到 MT+P，保留原始删复原修正

三份源码，共 641 行。原完整 task_complete=false，batch_target_complete=false，batch_target_source_complete=false，local_step_complete=true；未编译、正式信用 0。E 三份 Lean、REGISTRY、REPORT 已重新核对 raw SHA 并保持冻结。

`Part3MediumNativePrincipalSource.lean` 是独立源数据和有限中心化，不导入任何 F S1/S2/variance 估计。nativeMT 使用实际 lambdaTrim、primitive q、active d、paperPsi、完整 B_r；nativeRestoredZero 是 fully-restored A_r 模型。通过已存在的有限 residue centering 推出模型为 MT+centered source，实部为 MT.re+P；P 使用带 phi(ell)*c_ell(r,s) 的真实有限 Gram 形式，仅用旧 exact finite Gram 在构造的 common period 上证明非负。单位 b 上，形式代码的完整 (n,ell*r)=1 与原稿 A_r(b) 的 (n,r)=1 门精确一致。没有额外强制 (r,ell)=1。

`Part3MediumActualS3ZeroCentering.lean` 才完成真实源与模型之间的桥。nativeGenuineZero 直接按 E fibreCarrier 的 headCoefficient*E.zeroMode 定义，保留物理 lcm 和两个原始 alpha 标签；证明其等于真实 nativeCRTZero。实际 clean gate 仅为 (r,s)=(s,ell)=1，允许 r 与 ell 共享素因子。此时 CRT coefficient 精确等于 phi(ell)*c_ell；全部非 clean 对的逐项差额单列为 roughReplacementCorrection，未宣布它为零。由此真实 all-label 零模=MT.re+P+rough correction；实际 off-diagonal 零模再减 genuineDiagonalZero。并非仅凭函数名把 restored 模型当作真实 Poisson 源。

`Part3MediumActualDeletionBudgets.lean` 给真实零模的 inverse-lcm absolute kernel，进而给 diagonal/gcdBad/close-pair 原 source 的 norm 上界；证明真实 alpha diagonal 对数恰为 Ncard，close-pair 数不超过 Ncard*(2*ceil(T)+1)。offset 编码保持自然数差的信息，包括零端点。这些是有限真实预算和 occupancy 端口；尚不能冒称为原稿要求的任意 log 节约。shifted Shiu/gcd averaging、完整 weighted outer aggregation 与两个单零项的 Rcal*(N+Y) 支付仍未完成，因此完整 F target 明确未达成。

S1、S2、variance 只单向消费独立 nativeMT/nativeP 源身份；本中心化没有使用其后续 Gram 界或 spectral 结论。S2 的实际零模/恢复身份尚待最终 intake 后统一组合，未当作本源码前提。未发现原稿缺口；剩余是实际删项定量及整体 source assembly 的实现工作。

三个新源、直接导入安装映射、前批冻结与现有 supplier raw SHA 均在 REGISTRY.json 中。未执行 Lean/lake、内核、checker、CI 或额度检查。
