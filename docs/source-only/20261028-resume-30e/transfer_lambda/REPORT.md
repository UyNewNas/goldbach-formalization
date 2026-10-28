# transfer_lambda E 源码交付

本轮完成的窄步是 production FULL16 STATIC near-cap 系数 `sigma` 的真实物理四坐标原子重构，以及同一 signed count−exact coprime mean 的精确线性展开。原完整目标 `task_complete=false`；本轮全部目标 `batch_target_source_complete=false`；这个必要局部步骤 `local_step_complete=true`。`compiled=false`、`formal_credit=0`。

## 原稿与真实对象

已核原稿 `manuscript-body.tex` 第258–280行的 `eq:current-PP`：独立测试词 `u` 上的固定 smooth `W_N`，count 与 exact coprime mean 使用同一个 signed `rho_N`。第282–357行另要求真实因果 policy、完整物理系数、原始词到 HB/chart 的精确身份及有限 scalar mass 支付。

这里直接读取已独立定义的 `U1011OriginalSixteenJointNearCapModulusConvolution.sigma`、`marks`、`modulus`，通过 production `U1011ActualSigmaBoxAtomAssembly` 已证明的原始 unique-owner/state 分割连接。未将两边定义成 candidate 来关闭身份，未把该 sigma 与 `jointPresievedSigma` 交换。

## 两个源码的实质步骤

1. `P5ActualNativeSigmaPrimeProductAtoms.lean`：对真正 mark，由 original `owner` 和非零 `chosenTag` 给出 `boxPolicy_certificate` 的真 `wholeBoxEligibleTest`，并由 `compiled_static_on_cell` 得到 exact near-cap row support/coefficient。将 production actual sigma→physicalTest 的真实 low/U11 分解提升到 `Part3.primeProductSignedError`。随后从原 low/base/removed-row 的实际 inner/outerCells 展开 smooth sigma，所有负号和重复 occurrence 保留；fullPrefix×d 与 native residual coefficient 仍在原 physicalTest 中。由原 `actual_sigma_smooth_reserve_identity` 定义显式 `reserveSigma`，证明 sigma=smoothSigma−reserveSigma，并对相同 Q、相同系数的 count 与 exact mean 同时保留这个身份。literal 17572-row deletionMask 由原 production mask dictionary 接入。

2. `P5ActualNativePhysicalAtomOrderedFields.lean`：finite bank 从真实 active owner、State、low/base/removed-row 的实际 box sets 抽取，而不是任取 Family。证明三类实际 occurrence 都在 bank，并恢复真 whole-box branch licence。`physicalBoxAtom_eq_profile` 连接两个原先独立存在的定义：production physicalBoxAtom 与 peer 的 smooth zero-extended prime-coordinate profile。消费 pp_derivatives E 的真实 ordered derivative dictionary，得到同一个常数先于 N、点、ordered word 的预算，另得 real smoothness、实际 native floor 与逐点幅度0≤profile≤1。这个 bank 只为导数选统一常数；原系数展开中的重数与符号没有被去重。

## 精确范围与未完成项

这是既有 FULL16 **系数侧 physical t4 原子**的重构。外部 PP 测试词 `u` 的 rank r、cap P、weight W 始终独立；任意 W 的线性身份不构成 W 的 geometric licence。physical t4、residual rough coordinates 与独立 u 不作等同。

本轮没有 lower actual compiled CapPlan→独立 original selected caller 的所有 term association。lower_square 已明确其当前 selectedLowerData/pairPlan 仍是 candidate receiver；lower_chambers 的 true mesh/local query 结果也没有给出全部 adopted source-bank association。没有将这些缺项当作新结论性前提。

本轮没有独立 u-side 的所有实际 present-rank ordered Family cover，也没有原始 prime source→完整 HB/dyadic/chart atlas 的最终 exact binding。peer E 可证明真实 log atom 的全部有序导数，但这本身不提供上述算术 caller 归属。旧 all-K Lambda/proper-power 结果仍需这个实际 independent Family 与完整 chart multiplicity/scalar sum 才能结束原转移。

`reserveSigma` 目前只有真实精确差身份。production 原 native/low error support 可用于后续付款，但本轮不宣称全 q asymptotic reserve、total mean norm 或原完整 PP 已付。此前 D 的独立 sharp selected atom 也不会据此自动成为所有 lower/adopted caller。

未发现新原稿数学反例；以上是源码实现/接口缺口，不能登记为已证明的原稿缺陷。

## 依赖、安装与静态验证

两个本轮文件依次安装到同名 `ImbalancedChen/` 路径。第二个依赖 frozen E peer `P5ActualRankLogAtomEuler.lean`（SHA `3bc1f86a097d45f36434b031e581d2958db2cf377adf91332d73ba72d12c911c`），其 transitive imports 按 peer REGISTRY 的 exact map 安装；其中 D dictionary 使用 root 授权修名后 SHA `f40cd3b0dbe177c9b2d9d2df3bd6b2f010601f0592a766119456a46bff05d9bb`。全部 production declaration source 与 raw SHA 已列本轮 REGISTRY，先前 D 未修改。

仅做原稿/源码静态审读、声明/禁用 token 检查及 raw SHA。没有 Lean/lake/compiler、大型 checker、额度查询或新代理。

## 本轮 raw SHA

- `P5ActualNativeSigmaPrimeProductAtoms.lean`：`b3b1a7e71ee7dea6d71b404282a4e008eee138cc38a4b472bac1aea1fafbda09`；237 行，12 个声明。
- `P5ActualNativePhysicalAtomOrderedFields.lean`：`f773588f494aa0013619ffaa63843cd335b52e3a8b8fe4e289058d696810822e`；142 行，12 个声明。
- `REGISTRY.json`：`1c0ca2293bf2e392b4a707554c8688fe81915d2f04725c70431290705df36e37`。

REPORT 自身 raw SHA 在冻结通知中给出，避免自引用哈希。
