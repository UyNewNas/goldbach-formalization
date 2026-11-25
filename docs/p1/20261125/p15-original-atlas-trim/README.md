# 原 singleton Atlas 的 trim 支付

状态：`SOURCE_IMPLEMENTED_REVIEWED_NOT_COMPILED`。这组文件尚无新的 P1 编译、独立内核或完整自有声明验收回执，不据此改变整个 P1.5 的节点状态。

## 首次依赖编译后的精确修订

发布提交 `e1a80f6c306b58eadf2a8c6f58f4cbc7385e32d5` 的 153 模块清单、验证器及静态回执保存在 `snapshots/source153-before-first-compile/`。随后 P1 对两个 Mathlib-only provider 的首次编译暴露了五处表达问题，精确修订由相邻 proper-power 目录的 `FIRST_COMPILE_REPAIRS.json` 单独绑定：Core 显式使用素数大于一并反转已有素数幂表示的等式；Mellin 补全 `integrable_zero` 参数、展开点态比较目标，并给有限和的整个被加项补括号。这些变化均在证明体内部，声明、假设及 imports 保持不变。

当前 trim 清单只更新这两个 provider 的源码指纹，仍有 153 个模块，三阶段联合仍为 356。验证器先按五个确切字节区间重建旧 provider，再检查原 371→153 分层记录，最后独立检查当前 153/168/316 项源码及其联合图。原 `PROVIDER_ADOPTION.json`、`SOURCE_REVIEW.json`、`DEPENDENCY_TRANSITION.json` 与原九条 Core 声明的分层来源均保持原样。此次静态回执仍不代表 Lean 验收。

## 第二次 Mellin 表达修复

`ef450be0a89b6a3f88b3bca19d06e04e7967fa18` 的实际 P1 验收已接受 Core；Mellin 留下一处零函数可积性的 `ContinuousENorm` 实例路径不匹配。相邻 `SECOND_COMPILE_REPAIRS.json` 只将 `integrable_zero Ω ℂ μ` 换成项目固定 Mathlib 中已有的 `integrable_const_iff.mpr (Or.inl rfl)`。当前源码、声明和 import 的其余字节保持不变；Core 源码及其已成功验收不重做。

当前验证器先逆转这个单一字节区间，重建第一次修复后的 Mellin，再逆转原五处修复核对初始 153 项快照。当前 trim 清单仅再更新 Mellin 一行并绑定独立的第二次修复 manifest，153/168/316 与联合 356 的集合均不变。前次当前记录保留在上述 Git 提交，原历史清单和修复记录不改写。此处依然只是源码核验，不能代替 trim 两目标的实际编译。

## 原对象和有限恒等式

`P1OriginalSingletonAtlasTrim` 保留原 `trimReserve (actualLicence kap B N) (2*N) N kap0 Q rho`，其被丢弃的实权为

\[
\left(1-\eta\!\left(\frac{p}{N^{1-\mathrm{kap0}}}\right)\right)
\operatorname{smoothNatural}(\mathrm{kap},B,N,p).
\]

这里 `kap0` 是额外完整乘积 trim 的参数，`kap` 是原 profile 的下界参数，两者独立保留。`original_singleton_trimReserve_eq_signedError` 先把这笔原 reserve 精确识别为同一 `Q`、同一有符号实 `rho` 的 singleton discrepancy。`original_singleton_trimReserve_eq_prefix` 再利用权重在原 lower cut 以上为零，将素数载体限制到原 prefix。两个步骤同时保留同余计数与精确互素均值，没有把均值改成总质量。

## 终端定理

`eventually_original_singleton_atlas_trim_singularNormalization` 的顺序是：先固定 `kap0,tol`，假设 `0 < kap0 < 1`、`0 < tol`，取得充分大 `N` 的阈值；阈值之后才选择任意 `kap : ℝ`、`B : ℕ`、`Q : Finset ℕ` 和 `rho : ℕ → ℝ`。在

\[
Q\subseteq[1,N],\qquad |\rho(q)|\le1\quad(q\in Q)
\]

下，结论为原 trim reserve 的复范数不超过 `tol * singularNormalization N`。它不要求 `Even N`，也没有把最终误差界放入前提。

证明复用原 `exists_prefix_primitive_budget`，取 `eps = kap0/2`、`Y = originalLowerCut kap0 N`、`M = N`。应用除数预算前先使用已有定理证明 `Y < N`，所以不对零差 `N-p=0` 使用除数界。所得三个次线性 power-log 项分别用已有归一化预算吸收。

## 已有算术工作的复用

`P5OriginalSingletonLowerTrimPaid` 从既有 `docs/source-only/20261028-resume-30f/transfer_lambda/` 文件完整原字节接入 canonical 路径；全部证明体和 import 保持不变。其源 Git blob、SHA-256 和路径见 `PROVIDER_ADOPTION.json`。本次没有重新证明 divisor subpower、倒数 totient 和式或 prefix 算术预算。

原 `P1OriginalSingletonMiddleWeight.lower_paid` 支付的是另一笔 sharp-to-smooth `lowerReserve`，其合同不能直接替代此处原 Atlas 的 `(1-eta) * smoothNatural`。本接口仅补有限字典、支撑与已有预算的实例化。

稿件依据固定为 `UyNewNas/chen-imbalanced-semiprimes@a988cba584d803ae2856a0de50efb582f4f3dd6a` 的 `paper/release-20261106/en/coefficient-appendix.tex`（blob `10f3e2efb2074a9b97148a5151956e1d450be13f`）中的完整乘积 trim 段。

## 当前 153 项源码闭包与显式过渡

当前 `SOURCE_CLOSURE.json` 为 v2，两个目标仍是 `P5OriginalSingletonLowerTrimPaid` 与 `P1OriginalSingletonAtlasTrim`，项目源码闭包为 **153 项**。这两个 owner 的字节分别与 `PROVIDER_ADOPTION.json`、原独立 `SOURCE_REVIEW.json` 完全相同。

原 371 项清单保存在 `snapshots/initial-source371.json`；`DEPENDENCY_TRANSITION.json` 明确记录到当前阶段的变化：

- 保留的 152 项中，141 项原字节不变；11 项变化分别来自阶段 1 的 `PointwiseData` 精确语法修复、9 项既有已验收 reindex postimage 的原样采用，以及完整 AllK 的 import-only 分层。
- 新增的唯一项目模块是 `Part3FiniteLambdaOverLogCore`。它使用原 namespace、原九条有限字典声明和原证明字节，literal imports 为 `Mathlib`。
- 219 项退出这组目标的 import 闭包，canonical 文件全部仍存在。其中 218 项原字节不变；旧 `Part3FiniteLambdaOverLogDictionary` 保留为已授权的完整 provider 互补 postimage。退出当前闭包不表示模块无用、没有其他接受记录或从未处理。

结合当前阶段 1 和六目标阶段 2，范围如下。集合有重叠，不能把各行数量直接相加。

| 范围 | 项目源码数 |
|---|---:|
| 阶段 1 | 316 |
| 当前阶段 2：Core + 原五目标 | 168 |
| 阶段 1 ∪ 当前阶段 2 | 349 |
| 当前 trim 两目标闭包 | 153 |
| 阶段 1 ∪ 当前阶段 2 ∪ trim | **356** |

trim 向阶段 1、2 的联合范围增加 7 项：本 consumer、原 `LowerTrimPaid` provider，以及 `P5OriginalPrimeEndpointDivisors`、`P5OriginalPrimeEndpointLogPayment`、`P5OriginalSharpPrimeSynthesis`、`P5PrimeDivisorMeanCorrection`、`P5zElevenErrorTransport`。这些是源码集合归属，不是新增编译或接受数量。

`CURRENT_STATIC_RECEIPT.json` 独立绑定原 provider adoption、原 source review、371 项快照、三份明确的来源变更 manifest、当前 153 项图及当前阶段 1／2 的图。核验同时用保存的 preimages 和已记录的精确 byte splices 在内存中复原旧 371 项源码，检查旧、新真实 imports、全部变化归属、无缺源／无环，以及 356 项联合范围。

只读复核命令：

```bash
python docs/p1/20261125/p15-original-atlas-trim/verify_current_sources.py
```

该脚本只使用 Python 标准库读取本地源码与元数据；不调用 subprocess、Lean、云或缓存。它固定当前输入 pins，遇到未记录的变化会停止。已有 receipt 由显式 `--write-receipt` 首次创建，脚本不会覆盖它。静态结果不构成 elaboration、kernel、完整自有声明或 receiver readiness 的验收。

## 验收和整体边界

新 consumer 已经独立进行源码合同与 Lean API 静态审查，结果见 `SOURCE_REVIEW.json`。静态审查不能替代 elaboration 或内核检查。其依赖包括同轮 original licence 与 original AllGroup reserve providers；须先复用或验收这些实际依赖，再通过既有 P1 normal/kernel/full-owned 流程。

此项与原 Atlas proper-power 支付分别处理两笔显式修正。原 signed von Mangoldt 分布误差、medium Atlas、remaining Type-I Atlas，以及完整原系数与历史余项合并仍须独立闭合。
