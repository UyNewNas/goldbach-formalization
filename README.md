# Goldbach 1+1.75：Part A 的 Lean 4 形式化

本项目推进 Slava Chan《Theorem (1+1.75) on the Goldbach Conjecture》**2026 年 11 月 6 日冻结版**的 Lean 4 形式化。本次从 `master` 导航页集成 Part A 的精确计数、实指数、半乘积质量、归一化和条件式数值转移，纳入 **69 个既有项目模块、1880 个去重声明**；详细来源与验证边界见 [Part A 集成记录](docs/PART_A_INTEGRATION_20261125.md)。

**Part A 的组合入口已通过本轮编译、内核重放及完整声明审计。** 当前验收覆盖 69 个项目模块及新根入口，共 1880 个去重声明，见 [本轮验收回执](verification/part-a/current/RECEIPT.json) 和 [原始证据](verification/part-a/current/)。**整篇主定理尚未完成无条件形式化**，实际 `hLower`、`hUpper` 仍待后续供应。

[1106 稿件与数值材料](https://github.com/UyNewNas/chen-imbalanced-semiprimes/tree/a988cba584d803ae2856a0de50efb582f4f3dd6a/paper/release-20261106) · [1106 中文正文源](https://github.com/UyNewNas/chen-imbalanced-semiprimes/blob/a988cba584d803ae2856a0de50efb582f4f3dd6a/paper/release-20261106/zh/introduction.tex) · [完整进度看板](https://goldbach-formalization-board-20261107.slava2333.chatgpt.site/) · [主分支集成范围](docs/PART_A_INTEGRATION_20261125.md)

## 数学目标与计数口径

稿本研究充分大偶数的表示

$$
N=p+rq,\qquad p,q\text{ 为素数},\qquad r=1\text{ 或为素数},\qquad r\le q^b.
$$

`D_b(N)` 按不同素数加项 `p` 计数，每个 `p` 只计一次；素数余项 `r=1` 保留。`D12` 排除余项 0、1；坏半素数采用唯一排序 `r ≤ q`，保留平方余项，不增加因子 2。主参数为实数 `1/2 < b < 1`；项目简称 **1+1.74817** 对应主要端点 `b=0.74816964`、`a=1+b=1.74816964`。

以稿本奇异级数归一化 $H_N=C_NN/(\log N)^2$，完整目标为

$$
\liminf_{\substack{N\to\infty\\2\mid N}}\frac{D_b(N)}{H_N}
\ge c-K\log(1/b),\qquad
c=\frac{49044063}{25000000},\quad K=\frac{8452171}{1250000}.
$$

| A5 的既定端点 `b` | 充分大偶数的目标下界 |
| --- | --- |
| `0.74816964` | $10^{-5}H_N$ |
| `0.74816865` | $10^{-6}H_N$ |
| `0.9` | $1.24889H_N$ |

这些端点的严格标量余量和共同阈值组装已在历史组件中验收；实际计数的上、下界前提仍需后续证明。1106 稿本另有 `b=3/4` 的主标题推论，其范围与上述三端点分别记录。

## Part A 的边界

| 节点 | 本次集成内容 | 尚未由该项提供的结论 |
| --- | --- | --- |
| A1 | `D12_eq_RealDb_add_RealB`：按每个 `p` 的精确有限分解 | 渐近上、下界 |
| A2 | 实际半乘积源与唯一有序素数对重索引；保持严格计数端点和平方 | 筛后坏表示的完整估计 |
| A3 | 固定 PNT/Mertens 供应推出未筛源质量 `J_b=log(1/b)`，含稿本幂次截断 | 实际正上界筛转移及 `hUpper` |
| A4 | `C_N`、`H_N`、Euler 乘积与固定正幂截点归一化 | 整个 P4 或完整主定理 |
| A5 | 精确 `c/K`、三个端点、条件式共同阈值推论 | `hLower`、`hUpper` 的实际解析供应 |

A3 最终 supplier 定理直接调用固定依赖中的 PNT 与 weighted Mertens 定理，已无这两项结论的显式假设参数；这些外部定理的固定依赖仍保留。本次只复用该供应链。A3 的质量单位是 `N/log N`，不能直接替代实际坏表示的 `H_N` 归一化上界。

[`CurrentMainTheorem.lean`](ImbalancedChen/CurrentMainTheorem.lean) 保留 `hLower` 和 `hUpper`：分别针对实际 `D12` 与实际有序坏半素数计数。完整闭合还需同一实际系数的筛、密度、分布及数值证书论证。

## 固定环境与复验

根文件 [`ImbalancedChen.lean`](ImbalancedChen.lean) 只导入 `RealHalfProductMassSuppliers` 和 `UniformPowerEulerNormalization`，通过其依赖覆盖上述范围。

- Lean：`leanprover/lean4:v4.33.0-rc1`。
- mathlib：`e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`。
- goldbach-lean：`09b97db5764ade1246bfb77206baa1b124760958`。
- 完整依赖锁定见 [`lake-manifest.json`](lake-manifest.json)；历史证据见 [`verification/part-a/original/`](verification/part-a/original/)。

```bash
python3 verification/part-a/verify.py
python3 verification/part-a/verify_current.py
```

以上命令核对保留证据与当前源码的对应关系；它们不重新运行 Lean。实际构建、内核重放和声明导出命令见 [本轮运行记录](verification/part-a/current/)。

69 模块是两份历史验收闭包的去重并集。本轮在固定提交 `c34982b300858968ae78403d3fbd306b88236c10` 上单独完成新根的联合验收，原始六份证据保存在 [本轮证据包](verification/part-a/current/evidence.zip)。验收不接受 `sorry`、自定义数学公理或信任绕过；允许的标准公理为 `propext`、`Classical.choice`、`Quot.sound`，并须检查声明的传递依赖。

## 后续开发与历史导航

其余部分继续在开发分支推进。以下入口保留原导航用途，各分支内容和验收范围须以精确提交及记录为准：

| 入口 | 内容 |
| --- | --- |
| [集成分支 / PR #4](https://github.com/UyNewNas/goldbach-formalization/pull/4) | `codex/chen-parts-integration` 的组件集成与归档证据 |
| [续推分支 / PR #5](https://github.com/UyNewNas/goldbach-formalization/pull/5) | `codex/proof-continuation-20261015` 的证明开发与候选 |
| [完整源码编译 / PR #6](https://github.com/UyNewNas/goldbach-formalization/pull/6) | `fix/full-source-compilation-20261024` 的独立编译覆盖工作 |
| [历史定理映射](https://github.com/UyNewNas/goldbach-formalization/blob/codex/proof-continuation-20261015/docs/CURRENT_MANUSCRIPT_MAP.md) · [证明状态](https://github.com/UyNewNas/goldbach-formalization/blob/codex/proof-continuation-20261015/docs/PROOF_STATUS.md) | 按其中注明的稿本版次和源码版本阅读 |
| [外部证明复用](https://github.com/UyNewNas/goldbach-formalization/blob/codex/proof-continuation-20261015/docs/EXTERNAL_REUSE.md) · [历史开发说明](https://github.com/UyNewNas/goldbach-formalization/blob/codex/proof-continuation-20261015/README.md) | 固定依赖、兼容性、许可与组件历史 |
| [固定源码批次](https://github.com/UyNewNas/goldbach-formalization/blob/86690fc4872804c1e0ede28299f8cb6a91e62285/docs/source-only/20261025-code-only/batch1/README.md) | 2026-10-25 未验收候选的原始总账 |
| [完整编译报告](https://github.com/UyNewNas/goldbach-formalization/blob/fix/full-source-compilation-20261024/docs/FULL_SOURCE_COMPILATION.md) · [开发 CI 工作流](https://github.com/UyNewNas/goldbach-formalization/blob/codex/proof-continuation-20261015/.github/workflows/lean.yml) | 独立开发分支的构建、内核重放与声明审计 |

English: this integration contains Part A only. Historical component acceptance and the new combined-root verification are separate records. The complete manuscript theorem remains open in Lean.
