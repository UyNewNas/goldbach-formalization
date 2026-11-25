# Part A 集成记录 · 2026-11-25

## 范围与当前状态

本次以原来仅有导航 README 的 `master` 为基线，纳入 Part A 的既有源码和证据。组合范围为 **69 个项目模块、1880 个去重声明**，另加一个仅导入两个目标模块的根文件 `ImbalancedChen.lean`。声明数包含定义与引理等，不是全项目定理数。

历史组件已在各自明确范围内验收；**本次新根的编译、内核检查及传递公理检查尚待完成记录**。本轮输出见 [`verification/part-a/current/`](../verification/part-a/current/)，不能以历史成功记录替代新根的 receipt。完整主定理仍有实际解析前提。

## 冻结来源与闭包合并

数学源基线为 [`b7b0f5613f1b34855e0da7ad44d1d79ed34519cf`](https://github.com/UyNewNas/goldbach-formalization/tree/b7b0f5613f1b34855e0da7ad44d1d79ed34519cf)。各模块以原始 manifest 的路径、字节哈希及明确选版为准；验收 driver 提交不是所有数学模块的统一源版本。

| 范围 | 项目模块 | 声明 | 原验收 |
| --- | ---: | ---: | --- |
| A1/A2/A3/A5：`RealHalfProductMassSuppliers` 闭包 | 24 | 558 | [run 44470415535](https://github.com/UyNewNas/goldbach-formalization/actions/runs/44470415535) |
| A4：`UniformPowerEulerNormalization` 子闭包 | 56 | 1580 | [run 44440822784](https://github.com/UyNewNas/goldbach-formalization/actions/runs/44440822784) 的 208 模块闭包内 |
| 两者共享 | 11 | 258 | 按模块身份和声明去重 |
| 本次并集 | **69** | **1880** | `24+56−11`；`558+1580−258` |

A3 driver 为 [`34f7b3f0516991fe1a9dbe3a08bf76c691d09080`](https://github.com/UyNewNas/goldbach-formalization/commit/34f7b3f0516991fe1a9dbe3a08bf76c691d09080)，[原 manifest](https://github.com/UyNewNas/goldbach-formalization/blob/34f7b3f0516991fe1a9dbe3a08bf76c691d09080/verification/parts/p0/a3-mass-api/candidate-manifest.json) 无 overlay。

A4 driver 为 [`f7ea5972d361d67850dd67292c993d782a73b8a4`](https://github.com/UyNewNas/goldbach-formalization/commit/f7ea5972d361d67850dd67292c993d782a73b8a4)，[原 manifest](https://github.com/UyNewNas/goldbach-formalization/blob/f7ea5972d361d67850dd67292c993d782a73b8a4/verification/parts/p0/p4-eighth-api/candidate-manifest.json) 对应完整的 eighth parent physical ledger 验收。本次只提取 A4 所需的 56 模块子闭包。

A4 子闭包保留六个原 manifest 明确的依赖 overlay：`FirstExitTree`、`FiniteSieveModel`、`PhysicalUpperWeightBridge`、`SmallRoughMainTerm`、`ActualSmallRosserDensity`、`ChenInitialPrimeSource`。其余模块也按 manifest 核对，不能直接用开发分支最新文件替换。

这 69 个源文件来自两份历史闭包的并集，**不称历史上曾有一次 69 模块的联合编译或验收**。A4 的 208 模块成功运行也不等于整个 P4 或主定理已完成。

## 原始证据存放

| 文件 | 用途 |
| --- | --- |
| [`original/a3.zip`](../verification/part-a/original/a3.zip) | A3 历史完整原始 artifact ZIP |
| [`original/a4.zip`](../verification/part-a/original/a4.zip) | A4 所在历史完整原始 artifact ZIP |
| [`original/a3-manifest.json`](../verification/part-a/original/a3-manifest.json) | A3 24 模块的精确选源记录 |
| [`original/a4-manifest.json`](../verification/part-a/original/a4-manifest.json) | A4 所在完整历史闭包的精确选源记录 |

原包完整保存，组合源码和本轮验证输出另记。源文件相同、历史组件通过和当前根通过是不同的证据命题。

## 与 1106 稿本对应

本次稿件固定为 [`chen-imbalanced-semiprimes@a988cba584d803ae2856a0de50efb582f4f3dd6a:paper/release-20261106`](https://github.com/UyNewNas/chen-imbalanced-semiprimes/tree/a988cba584d803ae2856a0de50efb582f4f3dd6a/paper/release-20261106)，中文与英文正文源均在该目录。10 月版映射只作历史资料；以下采用 1106 的公式标签。

| 节点 | 验收范围 | 1106 对应位置与边界 |
| --- | --- | --- |
| A1 | `D12_eq_RealDb_add_RealB`，实指数下按每个加法素数一次的有限分解 | `introduction.tex` 的 `eq:current-d12`、`eq:current-db`、`eq:current-bb`、`eq:reduction` |
| A2 | `realHalfProductSource_existsUnique_pair`、`realOrderedBadReceiver_factors_unique` 等唯一重索引 | 唯一排序 `r≤q`；平方保留；从源的 `m≤N` 恢复计数的严格过滤 `m<N ∧ Prime(N−m)` |
| A3 | 实际未筛半乘积源质量极限 `J_b=log(1/b)` | `argument.tex` 的 `eq:current-pair-measure`、`eq:current-bad-mass`；稿本截断 `2N^(1−κ)` |
| A4 | `C_N`、`H_N`、Euler 乘积与固定正幂截点归一化 | `eq:current-normalization`、`eq:current-mertens`；`sieve-appendix.tex` 的 `sv:euler-ratio` |
| A5 | 精确 `c/K`、三个端点和条件式共同阈值 | `eq:current-safe-constants`、`eq:current-main-count`、`eq:current-secondary-count`、`eq:current-common-exponent`、`eq:current-rational-margins` |

计数始终按不同素数 `p`：`r=1` 的素数余项属于 `D_b`，`D12` 要求 `N−p>1`，而 `p<N` 排除零。主定理固定实数 `1/2<b<1` 后令 `N` 沿偶数趋于无穷。排序不增加见证重数；平方余项在 `b<1` 时属于坏半素数。

A3 最终 `tendsto_realHalfProductSource_manuscriptCutoff_mass_of_suppliers` 只显式要求 `0<b`、`b<1`、`0<κ`；PNT/Mertens 结论已由固定依赖中的定理供给，未作为调用者的新假设。它依赖既有 `goldbach-lean`，本次不重新形式化这些稿外输入。

A3 的极限是源计数除以 `N/log N`；实际坏表示仍要经过补数素数过滤、许可的平滑外逼近及同一实际系数的正上界筛，才能得到 `B_b/H_N` 的上界。历史 `N/log^10 N` 截断接口与稿本 `2N^(1−κ)` 接口分别保留。

A4 使用 $C_N=C_2\prod_{p\mid N,\,p>2}(p-1)/(p-2)$ 和 $H_N=C_NN/\log^2N$。1106 Euler tail 中整除目标数的因子为 `(p−2)/(p−1)`；固定正幂截点满足 $V_N(N^t)\sim2e^{-\gamma}C_N/(t\log N)$。它不改变 A2/A3 的单次计数口径。

A5 使用 `c=49044063/25000000`、`K=8452171/1250000`。三个端点为 `b=0.74816964`、`0.74816865`、`0.9`，对应下界为 `10^-5 H_N`、`10^-6 H_N`、`1.24889 H_N`；共同自然数阈值先于所有后续偶数 `N` 选定。实际 `hLower` 与各端点 `hUpper` 仍是明确前提，阈值非有效。

1106 的 `b=3/4` 主标题推论另列于稿本；本记录的 A5 声明清单保留既定的三个端点。

## 固定环境、入口与复验

| 项目 | 固定版本 |
| --- | --- |
| Lean | `leanprover/lean4:v4.33.0-rc1` |
| mathlib | `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1` |
| goldbach-lean | `09b97db5764ade1246bfb77206baa1b124760958` |

完整传递依赖按根目录 `lake-manifest.json` 锁定。根文件只有以下导入：

```lean
import ImbalancedChen.RealHalfProductMassSuppliers
import ImbalancedChen.UniformPowerEulerNormalization
```

从仓库根目录运行复验入口：

```bash
python3 verification/part-a/verify.py
```

本轮 receipt、日志与范围记录放在 `verification/part-a/current/`。在同一源码的新根检查完成前，本记录不声明组合后的编译或内核验收通过。验收须核对完整声明类型及传递公理；仅允许 `propext`、`Classical.choice`、`Quot.sound`，不接受 `sorry`、新增数学公理或信任绕过。

## 后续接入

后续工作应复用上述冻结组件，按实际需要接入 P1–P5 的供应结果。`CurrentMainTheorem` 中的 `hLower`、`hUpper` 仍需针对稿本实际对象、同一系数及正确归一化证明，再完成最终同实例组装。Part A 的集成不改变这些剩余义务。
