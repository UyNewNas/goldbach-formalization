# Goldbach 1+1.75：不平衡陈氏定理的 Lean 4 形式化

本项目用 Lean 4 形式化 Slava Chan 的 [《Theorem (1+1.75) on the Goldbach Conjecture》](https://github.com/UyNewNas/chen-imbalanced-semiprimes/tree/a988cba584d803ae2856a0de50efb582f4f3dd6a/paper/release-20261106)（2026 年 11 月 6 日冻结版）。该目录包含中英文手稿和复现材料。

**项目仍在进行中。** 默认分支已集成并核验 Part A 的组合入口；P1–P5 的源码与阶段性验收在各自的开发分支维护。当前 Lean 主定理仍需要实际计数的上下界前提，不是完整的无条件形式化证明，也不是二元哥德巴赫猜想的证明。

## 数学目标

稿本研究充分大偶数 $N$ 的表示 $N=p+rq$，其中 $p,q$ 为素数，$r=1$ 或为素数，且 $r\le q^b$。$D_b(N)$ 按不同的加法素数 $p$ 计数，同一个 $p$ 只计一次，保留 $r=1$ 的表示。以稿本的奇异级数归一化 $H_N=C_NN/(\log N)^2$，目标是对实数 $1/2<b<1$ 证明：

$$
\liminf_{\substack{N\to\infty\\2\mid N}}\frac{D_b(N)}{H_N}
\ge \frac{49044063}{25000000}-\frac{8452171}{1250000}\log(1/b).
$$

项目简称 **1+1.75**；更细的简称 **1+1.74817** 对应端点 $b=0.74816964$。这些是稿本目标，不是该仓库当前已验收的无条件结论。

## 源码与验收入口

- **Part A（默认分支）**：[集成说明](docs/PART_A_INTEGRATION_20261125.md) · [验收回执](verification/part-a/current/RECEIPT.json) · [复现说明](verification/part-a/current/README.md)。组合根入口已通过编译、内核重放和完整声明审计；范围是 69 个项目模块加组合根、1,880 个去重声明，不是全项目的验收统计。
- **P1–P5（开发与集成）**：[P1](https://github.com/UyNewNas/goldbach-formalization/pull/10) · [P2](https://github.com/UyNewNas/goldbach-formalization/pull/11) · [P3](https://github.com/UyNewNas/goldbach-formalization/pull/12) · [P4](https://github.com/UyNewNas/goldbach-formalization/pull/13) · [P5](https://github.com/UyNewNas/goldbach-formalization/pull/14)。各入口只收录其证据所覆盖的范围。尚待核验的候选、局部验收和完整节点验收应分开阅读，以记录中的源码提交和验证范围为准。
- **尚未闭合的主定理**：[CurrentMainTheorem.lean](ImbalancedChen/CurrentMainTheorem.lean) 的 `hLower` 和 `hUpper` 分别是实际素数或半素数计数的下界、实际有序坏半素数计数的上界。Part A 的精确计数、未筛源质量、归一化和条件式数值转移不替代这两个筛法估计。

## 构建与复验

默认分支使用 [Lean 4 v4.33.0-rc1](lean-toolchain)，依赖版本由 [lake-manifest.json](lake-manifest.json) 锁定。构建[库入口](ImbalancedChen.lean)只覆盖当前集成范围。安装 Lean 工具链和依赖后，可运行：

```bash
lake build ImbalancedChen
```

这是构建命令，不替代内核重放和完整声明审计。核对已经保存的证据，请见 [Part A 复现说明](verification/part-a/current/README.md)。开发分支的结果应按其固定版本和对应回执复验。

**English summary.** This repository formalizes the 6 November 2026 manuscript on imbalanced Chen bounds. The default branch contains the checked Part A integration; the P1–P5 review branches track other scoped results. The full real-exponent theorem remains conditional in Lean on the lower and upper bounds for the actual representation counts.
