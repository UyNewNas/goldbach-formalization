# P3.3：大 gcd、大 supported 分支和小核有限频窗

本目录记录 P3.3 的同源复用验收。交付建立在 P3 续推提交
`ef1479c272bdd6b24800fa10409d793f0a2fe95c` 上，把该分支缺失的 **38 个已有 Lean 模块**按原字节接入。
它们来自看板登记的源码快照 `7f5330cace31383f5626da526b476dd4b0f43376`。
所需仓库内导入闭包共 **93 个模块**：原分支已有 55 个且完全相同，缺失 38 个，没有同名源码冲突。

本次不重写已存在的证明，也不把证据核验脚本称为一次新的 Lean 编译。
验收结论由 [report.json](report.json) 给出；完整目标声明记录保存在
[declarations.json.gz](declarations.json.gz)，包含私有声明、完整类型和传递公理列表。

## 验收范围

P3.3 的终点是：**原始带符号差额的大 gcd、大 supported 分支已经支付，剩余小核可截到每个预先固定的正参数 eta 所确定的共同有限有符号频窗。**

令 `d : MediumAtom`，`x = d.scale = d.U * d.V`，

\[
W=\Bigl(\sum_{n\in d.\mathrm{betaCarrier}}|\beta_n|^2\Bigr)
  \Bigl(\sum_{p\in d.\mathrm{primitiveFirstFactorCarrier}}|\gamma_{1,p}|^2\Bigr),
\qquad Y=x^{\sigma/4},\qquad P_A=x^2/(\log x)^A.
\]

共享首因子载体是原始整数载体，包含满足互素条件的合数；变量名 `p` 不添加素数条件。

### 1. 先拆原复数和，再支付删除项

`MediumAtom.sharedFirstFactorNonzero_eq_threePairedSupportMasks`
对任意实阈值给出精确复数恒等式。写

\[
g=\gcd(N_1,N_2),\qquad s=\operatorname{supportedPart}(N_1/g,g),
\]

三个互斥分支为 `g > Ybeta`、`g <= Ybeta ∧ s > Ysupport`、
`g <= Ybeta ∧ s <= Ysupport`。等号归小支。原始有序对、共享首因子、CRT 兼容条件、复系数与取实部顺序均保留。

`actual_betaL2_gamma1L2_cleaned_deletedPairedSupportedNonzero_log_payment`
在 `Ybeta = Ysupport = x^(sigma/4)` 时证明

\[
W(\|K_{\mathrm{large\ gcd}}\|+\|K_{\mathrm{large\ supported}}\|)\le 2P_A.
\]

两个原始外层二次矩均已计入。大 supported 支的证明还分别保留和控制 whole-W、原始零模及非零模。

### 2. 原始差额已经接到同一个小核

`uniformAuxiliarySW_signedError_sq_le_cleanedSmallPairedSupportedNonzero_add_log_payment`
从原 `MediumAtom.signedError` 出发，得到

\[
\|\mathrm{signedError}\|^2\le W\operatorname{Re}K_\infty+C P_A.
\]

量词为：先固定族 `F : ι → MediumAtom`、除数阶数 `B, C0`、参数
`0 < sigma < 1/100`、`0 < c0`、`0 <= kappa <= sigma/100`，以及该族的
`MediumAdmissible` 和 `UniformAuxiliarySW` 输入；然后是
`∀ A : ℝ, A > 0, ∃ C > 0, ∃ x0 > 1, ∀ i`，在 `x0 <= (F i).scale` 时成立。
常数与门槛可以依赖整个固定族及其辅助 SW 输入，但先于变化的族成员。

辅助 SW 是原 alpha 的互素等差数列输入，其定义没有把剩余小核估计当作假设。
清理 alpha 的转移、原差额平方的清理代价、两大分支的支付均在已验收证明链中。

### 3. 同一小核的有限化

`actual_betaL2_gamma1L2_cleaned_smallSupported_FourierTail_log_payment`
与 `actual_smallSupported_smoothFiniteFrequency_log_payment`
分别对同一个完整小核证明硬窗、软窗误差。对每个预先固定的 `eta > 0`，令 `Z = x^eta`，有

\[
W\|K_\infty-K_{\mathrm{fin}}\|\le P_A.
\]

软窗在每个实际尾部 gcd `D` 上使用共同整数半径

\[
H_D=\left\lceil\frac{64ZQ_1Q_3^2Q_2^2}{DV}\right\rceil,
\qquad 0<|h|\le H_D.
\]

正负频率均保留，零频率排除；低通函数在 `|u| <= 1` 为一，在 `|u| >= 2` 为零。
门槛可依赖 eta，但先于变化原子。两种有限近似各自与完整小核比较，不声称彼此精确相等。

上述两条已验收不等式使用同一个 `W`、原子和支撑条件。取两个门槛的最大值，应用
`|Re z| <= norm z`，即有

\[
\|\mathrm{signedError}\|^2\le W\operatorname{Re}K_{\mathrm{fin}}+(C+1)P_A.
\]

这是两个既有接口的数学接线说明，本次没有另加未经编译的聚合 Lean 声明。
`actual_smallSupported_supportedCore_Cauchy` 继续给出软有限核在原外系数非零支撑上的精确重索引及 Cauchy 界。

## 与 1106 冻结稿的关系

稿件固定为 `chen-imbalanced-semiprimes@3ffa2d159c9974e2ca6d5f930c0f2c16baa0135e`，入口
`paper/release-20261106/en/main.tex`。本轮核对的 `analytic-appendix.tex` Git blob 为
`7cf3bbb16cd8924565eb439e474e0674f04631da`。

| 稿内环节 | 对应范围 |
| --- | --- |
| `argument.tex` 受限中区命题的三重 gamma 加权差额 | `MediumAtom.signedError` 使用实际 `q1*q2*q3` 模数及精确互素主项；当前定义与已验定义同字节，归约直接从这个原始差额出发。 |
| 公共因子清理与原误差恢复 | 历史证明以 same-first-factor 的 gcd / canonical supported 三分拆作更细的删除，在归约内回到原 signedError，不以额外 S3 识别作为假设。 |
| 第一次 Poisson 后的小核有限窗 | 已验代码采用固定 `eta > 0` 的 `x^eta` 放宽窗；1106 下游允许可选小幂损失。下游统一选 eta 并估计剩余小核仍属后续节点。 |

旧回执记录 10 月稿件哈希；保留该历史事实，通过定义、声明与 1106 原始命题的对应关系确认复用范围。
源码哈希与旧稿日期本身不代替稿本语义核对。

本结论不扩展到逐式复现 Lambda-d / S3 展开及每次精确乘积排除顺序、
把通用 `ContDiffBump` 识别成 `GevreyCutoff.cutoff`、精确 `(log x)^5` 紧窗、
第二次 Poisson 的 m 窗、统一 7/32 谱估计或完整中区及 P3 主命题。

## 完整目标声明记录

| 模块（`ImbalancedChen/` 下） | 按模块归属的记录数 |
| --- | ---: |
| `Part3ActualLargeGCDBetaMass` | 15 |
| `Part3CleanBetaLargeGCDMajorant` | 26 |
| `Part3PairedAlphaDeletion` | 47 |
| `Part3TransposedLargeGCDFourier` | 17 |
| `Part3SharedFirstFactorLargePairedGCDW` | 29 |
| `Part3SharedFirstFactorLargePairedGCDNonzero` | 65 |
| `Part3SharedFirstFactorLargeSupportedDeletion` | 111 |
| `Part3SharedFirstFactorSmallPairedSupportedReduction` | 21 |
| `Part3SharedFirstFactorSmallCoreFourierTruncation` | 33 |
| `Part3SharedFirstFactorSmallCorePrimeDifferenceReindex` | 7 |
| `Part3SharedFirstFactorSmallCoreSmoothFrequency` | 51 |
| `Part3SharedFirstFactorSmallCoreSquaredFinite` | 34 |
| `Part3SharedFirstFactorSupportedCoreCauchy` | 13 |
| **合计** | **469** |

按 `(module, name)` 计有 469 条记录；仅按 `name` 去重后有 468 个不同 Lean 名字。两个历史单模块库存均记录自动生成的
`MediumAtom.q1SliceAtom.eq_1`；两份完整类型与传递公理相同，核验器检查其一致性。
469 是完整声明记录数，不是 469 条新增数学定理，也不是 469 个全局唯一名字。

## 分层证据

| 层次 | 数量 | 已有证据与本轮检查 |
| --- | ---: | --- |
| 目标及历史内部依赖 | 46 模块，1,561 条声明记录 | warnings-as-errors 编译、字面模块名 stock leanchecker 重放、serialized/environment 完整名单、完整类型和传递公理。13 目标的 469 条包含其中，不再相加。 |
| `Part3DistributionTargets` | 1 模块，91 条声明 | c509267 基线报告，源码及 `.olean` 精确匹配历史 `Part3ComplexDispersion` 的输入。按报告继承，不声称本轮导出了其全库存。 |
| 冻结基础依赖 | 46 模块 | core run `44318928116` / artifact `14441606127` 的同源、同 pins 根构建、字面重放和根公理审计。不声称逐模块完整类型导出，也不声称其 CI 对象与历史生产对象的二进制哈希一致。 |

允许的传递公理仅 `propext`、`Classical.choice`、`Quot.sound`。Mathlib 及锁定 goldbach 外库保留原依赖边界；
本次不声称逐一重放全部外库。13 个目标的完整类型和传递公理核验不是抽样。

原始证据按既有路径保存在 `verification/proof-continuation/2026-10-15/`，选中文件未重写。
该处保留原总清单，但只安装本节点所需证据子集；其他清单条目不构成本次申领。
core ZIP SHA-256：`c9f5fae1810faa640c970bdd4db5f0efc20240f6c45cd409b58163829d189499`。

## 重现核验

仓库根执行：

```sh
python3 -B verification/verify_p33_acceptance.py \
  --report docs/part3-distribution/p3-3-acceptance-20261125/report.json \
  --declarations docs/part3-distribution/p3-3-acceptance-20261125/declarations.json.gz
```

缺源、源漂移、重放证据或完整库存异常均非零退出。[negative-controls.json](negative-controls.json)
保存六项负控制。无参数运行核验原始输入并打印重建报告，不比较或覆盖已发布的派生产物。
要独立检查发布产物，先将无参数 stdout 保存到临时文件后与 `report.json` 做 `cmp`，
再检查 `declarations.json.gz` 的 SHA-256 是否等于报告中的 `target_declarations_gzip_sha256`。

指定 Workspace Compile 27f68009 和备用 Cloud Compile 本轮均返回 HTTP 429，未启动新 Lean 编译。
本轮执行原始证据核验并复用同源成功回执。独立最终审查未发现 Critical 或 Important 问题；
已补明固定族与正 A 的量词，并说明发布产物的单独比对方法。

本地临时目录在发布前因执行环境存储异常变得不可用；使用同一远程源及证据恢复，原证明内容未变。
P3.3 的验收不改变 P3 父节点及后续谱估计、最终组装的开放状态。
