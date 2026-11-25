# P2.6 结构三 owner 独立只读审查

## 结论与执行边界

未发现阻碍三 owner 进入正式 P1 验收的实质数学问题。此报告固化已完成的审查，不重新执行数学试验。
本审查没有运行 Lean、leanchecker 或远端任务，也没有修改被审源码。
本地 copied-Core 原型通过不在此升级为实际 production owner 验收；实时 P1 状态应以主代理后续精确回执为准。

源码审查基线：`7770ba4e71cc0f1316f7558034aa9e1d498a18e6`。
新 owner 的实际 bytes/SHA 与原 manifest 相符；五份 retained 源码亦与该基线 Git blobs 逐字节一致。

## 原稿来源

- 仓库：`chen-imbalanced-semiprimes`。
- 原稿 pin：`a988cba584d803ae2856a0de50efb582f4f3dd6a`。
- 仓内路径：`paper/release-20261106/en/numerical-appendix.tex`。
- 实际读取路径：`/workspace/scratch/32a3e5d7265b/audit/sources/new/paper/release-20261106/en/numerical-appendix.tex`。
- 原始文件：42662 bytes，SHA-256 `bed33b90419c125c841e7dd4978042e8f663f41bbe5ab211caf6e701b5342232`。
- 已读位置：约 177–196 行，公式 label `num:simplex-moment`（188 行）。

原稿公式为

\[
\int_T \prod_{j=0}^d \lambda_j^{\alpha_j}\,dx
= d!\operatorname{vol}(T)\,
\frac{\prod_j\alpha_j!}{(d+\sum_j\alpha_j)!}.
\]

此轮沿用既有稿件审计提供的 upstream commit pin，读取并冻结本地原始字节，没有重新远端拉取稿件仓库。
Bounded Newton 和 duplicate-node 恒等式应记为从冻结 Core 定义推导的有限代数证明，用于连接原 producer 表达；不应记为 2026-11-06 稿明确陈述的 Newton 定理。

## 所审源码指纹

### 三个新 owner

| Module | SHA-256 |
|---|---|
| `ImbalancedChen.P2OriginalSaving19MomentAntidiagonalSplit` | `8fdac0d48e8d85b33ddc2e7c203e6275729243a76dfa67d962a25e811f806529` |
| `ImbalancedChen.P2OriginalSaving19HigherMomentsNewtonStructure` | `8fe12eb1fea30bf171ad999e4aebb76b25130332c8ae8937620ec5a3fd1a967e` |
| `ImbalancedChen.P2OriginalSaving19HigherMomentsMomentStructure` | `4c8250f09dfbd120c6e30bbbde047d5a31589b6e89713c2e2abe12a70dd6e885` |

### 五份 retained 源码

| Module | SHA-256 | 位于新 owner import closure |
|---|---|---|
| `ImbalancedChen.P2OriginalSaving19HigherMomentsCore` | `3738b75a69892c1f9ab68a395b6394817e24a94083ca5254b38c32d73a859832` | 是 |
| `ImbalancedChen.P2OriginalSaving19HigherMomentsGuardLowBoundary` | `3fa7f12eb715a9aabac0c431533fbb515ad3d2512aadd8eec677c5b098486604` | 否 |
| `ImbalancedChen.P2OriginalSaving19MomentFiniteReindex` | `ef69493b03eea3c013fe645f20f5a70b4348e64ec3c59aef1a0e325afa42e902` | 是 |
| `ImbalancedChen.P2OriginalSaving19HigherMomentsSymmetry` | `5425985922dae867d1a1be2903c2def751187894373d700ca3a8a62b3346e16d` | 是 |
| `ImbalancedChen.P2OriginalSaving19HigherMomentsSymmetryPilot` | `8cd95f3227fcbdd2172eb19df40f2553e53c34b375d45c80e20d444a131d3902` | 否 |

## 最终量词与前提

`integratedPower_newton_guard_structural` 对所有 `y : Fin 9 → ℝ`、`i : Fin 9`、`k : ℕ`，仅要求 `k ≤ 6`，得到

\[
\operatorname{integratedPower}(y,i,k)
=\frac{\operatorname{duplicateH}(y,i,k)}{9!\binom{9+k}{k}}.
\]

`duplicateH_author_guard_structural` 对所有 `y : Fin 9 → ℚ`、`i : Fin 9`、`k : ℕ`，仅要求 `k ≤ 6`，得到原 rational author 卷积式。
`duplicateH_eq_completeH_small` 的代数条件 `[CommRing A] [Algebra ℚ A]` 与原 `duplicateH` 定义一致。
辅助 Newton 关系的 `k ≤ 5` 对应总次数 `k+1 ≤ 6`。
没有新增节点互异、正性、非零节点、结论假设或已成立 guard 假设。

## 已完成的数学核查

1. **首指数分裂。** 映射 `e ↦ (e 0, Fin.tail e)` 的映入、单射、满射及被加项相等四项均完整。`j : Fin(k+1)` 提供 `j ≤ k`，故自然数截减恢复 `j + (k-j) = k`。`n=0` 与 `k=0` 均被覆盖。
2. **Newton 与递归界。** 列表归纳给出 degree 1–6 的 Newton 关系；strong induction 中 `k-j < k+1` 且递归次数仍 `≤6`。`y i :: List.ofFn y` 恰好额外复制一次 `y i`。逆元取消发生在 ℚ 中，`k+1 ≠ 0` 由自然数正性证明，无额外目标环前提。
3. **权重。** 两个相同首节点分配总次数 `j` 的 multiplicity 为 `j+1`，与 Core factored RHS 的 `e 0 + 1` 精确一致。没有丢掉 multinomial/factorial 系数或替换 `integratedPower` 定义。
4. **归一化。** `k!/(k+9)! = 1/(9! * choose(9+k,k))`，含 `k=0`；八维、九个重心坐标加一个权重后分母确为 `(k+9)!`。固定 degree 的 `norm_num`/`ring` 仍需生产内核验收。
5. **任意 index。** 使用 `y ∘ swap 0 i` 后，两条已接受 permutation 等式均将 index 0 送到 `i`。方向一致，`i=0` 也成立；与已接受 SymmetryPilot 的模式相同。
6. **数据与来源。** 未引入 archive 数值、Python 数学计算、替代 witness、外部估计或新公理。保留原 simplex-moment 供应商及原 Core 定义。

## 仍须经过的门禁

实际三 owner 的 normal、独立 kernel、完整 owned types/axioms、精确 published source/object closure 均不由这份静态审查代替。
生产 facade 此时未由本审查接回；后来接回时必须保持原公共接口。此结论不自动获得整个 HigherMoments 或 P2.6 endpoint 的完成信用。
无需为本审查重复编译已冻结的 Core、Low、FiniteReindex、Symmetry 或 Pilot。
