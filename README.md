# Goldbach 1+1.75: Lean 4 formalization of imbalanced Chen bounds

Work toward a **Lean 4 formalization** of Slava Chan's research manuscript *Imbalanced semiprime representations of even integers* (10 October 2026), concerning the **binary Goldbach conjecture**, **Chen's theorem**, and **imbalanced semiprimes**.

[Manuscript and numerical evidence](https://github.com/UyNewNas/chen-imbalanced-semiprimes) · [Read the manuscript PDF](https://github.com/UyNewNas/chen-imbalanced-semiprimes/blob/master/paper/SlavaChan-imbalanced-semiprimes-20261010.pdf) · [Development source](https://github.com/UyNewNas/goldbach-formalization/tree/codex/proof-continuation-20261015) · [Theorem map](https://github.com/UyNewNas/goldbach-formalization/blob/codex/proof-continuation-20261015/docs/CURRENT_MANUSCRIPT_MAP.md) · [Verification records](https://github.com/UyNewNas/goldbach-formalization/blob/codex/proof-continuation-20261015/docs/PROOF_STATUS.md)

**Status: formalization in progress. The manuscript's Theorem 1.1 and Corollary 1.2 are not yet completely formally verified.** The development branches contain both checked components and candidates awaiting verification. Each verification claim applies only to the revision and scope identified in its record.

## Find the code and current work

The default `master` branch serves as the public project entry point. The Lean implementation, build configuration and detailed progress records are on the development branches below. A default-branch checkout does not contain the Lean project.

| Branch | Role | Review entry |
| --- | --- | --- |
| [`codex/chen-parts-integration`](https://github.com/UyNewNas/goldbach-formalization/tree/codex/chen-parts-integration) | Integration and archived component evidence. | [Draft PR #4](https://github.com/UyNewNas/goldbach-formalization/pull/4) |
| [`codex/proof-continuation-20261015`](https://github.com/UyNewNas/goldbach-formalization/tree/codex/proof-continuation-20261015) | Ongoing proof development, including source-only candidates. Start here to inspect the implementation. | [Draft PR #5](https://github.com/UyNewNas/goldbach-formalization/pull/5) |
| [`fix/full-source-compilation-20261024`](https://github.com/UyNewNas/goldbach-formalization/tree/fix/full-source-compilation-20261024) | Separate work on complete source compilation coverage and compiler resource limits. | [Draft PR #6](https://github.com/UyNewNas/goldbach-formalization/pull/6) |

These branch roles were checked on 25 October 2026. The compilation branch and continuation branch have diverged; neither should be treated as containing all changes from the other. Consult the linked PRs and exact commits when reproducing a result.

## Mathematical target

The rounded project shorthand **Goldbach 1+1.75** refers to the manuscript's claimed refinement of Chen's theorem. A more precise rounded label is **1+1.74817**. In the notation $1+a$, $a=1+b$; the primary exponent is $b=0.74816964$, so $a=1.74816964$.

The manuscript studies representations

$$
N=p+rq,\qquad p,q\text{ prime},\quad r=1\text{ or prime},\quad r\le q^b.
$$

Distinct additive primes $p$ are counted once. With $D_b(N)$ denoting this count and $H_N=C_NN/(\log N)^2$ using the manuscript's singular-series normalization, the claimed general bound is

$$
\liminf_{\substack{N\to\infty\\2\mid N}}\frac{D_b(N)}{H_N}
\ge 1.96176252-6.7617368\log(1/b),\qquad \frac12<b<1.
$$

The stated eventual endpoints for sufficiently large even $N$ are:

| Imbalance exponent $b$ | Claimed lower count |
| --- | --- |
| **0.74816964** | $H_N/100000$ |
| 0.74816865 | $H_N/1000000$ |
| 0.9 | $1.24889H_N$ |

The complete formalization goal includes the arbitrary-real-exponent statement and the common-threshold corollary. The [current manuscript-to-Lean map](https://github.com/UyNewNas/goldbach-formalization/blob/codex/proof-continuation-20261015/docs/CURRENT_MANUSCRIPT_MAP.md) pins the manuscript source to [`ba6ec11`](https://github.com/UyNewNas/chen-imbalanced-semiprimes/tree/ba6ec11d800eccc54406490631895e174de85766) and records the exact constants and interfaces. These statements describe the target, not a completed unconditional Lean proof.

## Proof scope and remaining obligations

The implementation includes exact counting definitions, finite good/bad decompositions, rational coefficient arithmetic, sieve constructions, prime-sum and integral components, and numerical-certificate interfaces. The [verification records](https://github.com/UyNewNas/goldbach-formalization/blob/codex/proof-continuation-20261015/docs/PROOF_STATUS.md) distinguish component checks, accepted checkpoints and unfinished work.

In particular, [`CurrentMainTheorem.lean`](https://github.com/UyNewNas/goldbach-formalization/blob/codex/proof-continuation-20261015/ImbalancedChen/CurrentMainTheorem.lean) gives the real-exponent main-theorem interface with two remaining analytic premises:

- `hLower`: the required lower bound for the actual prime-or-semiprime representation count.
- `hUpper`: the required upper bound for the actual ordered bad-semiprime count.

Discharging these premises requires the corresponding sieve, distribution, density and certificate arguments for the manuscript's actual objects. Successful compilation of a component, a numerical replay or a historical checkpoint does not discharge the remaining premises.

## Reading and verification guide

| Entry | What to inspect |
| --- | --- |
| [Current manuscript map](https://github.com/UyNewNas/goldbach-formalization/blob/codex/proof-continuation-20261015/docs/CURRENT_MANUSCRIPT_MAP.md) | Mathematical statements, source edition and Lean interfaces. |
| [Proof status](https://github.com/UyNewNas/goldbach-formalization/blob/codex/proof-continuation-20261015/docs/PROOF_STATUS.md) | Dated verification boundaries, receipts and outstanding obligations. |
| [Development README](https://github.com/UyNewNas/goldbach-formalization/blob/codex/proof-continuation-20261015/README.md) | Detailed component history and development notes. |
| [25 October 2026 source-only checkpoint](https://github.com/UyNewNas/goldbach-formalization/blob/86690fc4872804c1e0ede28299f8cb6a91e62285/docs/source-only/20261025-code-only/batch1/README.md) | The dated candidate batch explicitly marked uncompiled and not accepted into the verified root. |
| [External proof reuse](https://github.com/UyNewNas/goldbach-formalization/blob/codex/proof-continuation-20261015/docs/EXTERNAL_REUSE.md) | Source pins, licenses, statement compatibility and transitive proof checks. |
| [Lean core workflow](https://github.com/UyNewNas/goldbach-formalization/blob/codex/proof-continuation-20261015/.github/workflows/lean.yml) | Build, kernel replay, axiom audit and declaration export stages for the continuation branch. |
| [Full-source compilation work](https://github.com/UyNewNas/goldbach-formalization/blob/fix/full-source-compilation-20261024/docs/FULL_SOURCE_COMPILATION.md) | Source coverage and validation work specific to the separate compilation branch. |

To inspect or build the project, select a development branch and follow that branch's pinned toolchain and verification instructions. A source inventory, source-only checkpoint or isolated green workflow is not evidence that every source or the final theorem has passed all checks.

The verified core does not accept `sorry`, custom mathematical axioms or trust bypasses. The permitted standard axioms are `propext`, `Classical.choice` and `Quot.sound`; accepted reuse must include checks of the selected theorem's transitive dependencies. Reports should identify the branch, commit, module and declaration, or the manuscript page and equation concerned.

## 中文说明

本项目推进**哥德巴赫猜想（哥猜）与陈氏定理改进方向的 Lean 4 形式化**，对应 Slava Chan 的《Imbalanced semiprime representations of even integers》2026 年 10 月 10 日版手稿。项目使用 **1+1.75** 作为近似简称，更精细的近似称呼为 **1+1.74817**；确切主参数为 $b=0.74816964$，次参数为 $b=0.74816865$。

默认 `master` 分支提供项目导航；实际 Lean 源码在上表开发分支中。请从 [当前开发分支](https://github.com/UyNewNas/goldbach-formalization/tree/codex/proof-continuation-20261015)、[定理对应表](https://github.com/UyNewNas/goldbach-formalization/blob/codex/proof-continuation-20261015/docs/CURRENT_MANUSCRIPT_MAP.md)和[验证记录](https://github.com/UyNewNas/goldbach-formalization/blob/codex/proof-continuation-20261015/docs/PROOF_STATUS.md)查看具体内容。完整源码编译修复在单独的 [PR #6](https://github.com/UyNewNas/goldbach-formalization/pull/6) 中推进。

主定理仍未完成无条件形式化闭合。已有局部核验结果与尚待编译、回放或审计的候选必须按提交和验收范围分别查看，不能把其中一项通过等同于完整证明通过。手稿 PDF、证明文本与数值复现材料见[手稿仓库](https://github.com/UyNewNas/chen-imbalanced-semiprimes)。
