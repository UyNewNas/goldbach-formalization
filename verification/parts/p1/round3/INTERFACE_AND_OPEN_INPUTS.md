# Part 1 历史第五层接口与未闭合输入

本接口使用共同数学基线 `1a80c1bcce67886f699d097fc37fd245cd3620bf` 和该基线冻结的手稿 `ba6ec11d800eccc54406490631895e174de85766`。接收时以本轮最终 `VERIFICATION.json` 绑定的实际目标源码为准。这里只解释已有 Lean 类型及它们的接入条件，不把最终密度界、积分数值界或有符号分布估计作为合法性假设。

## 1. 固定数据与坐标

`ImbalancedChen.HistoricalPrefixCapData` 的所有选盒数据先于目标 `N` 固定。数据结构本身没有 `N` 字段。

| 字段 | Lean 类型 | 约定 |
| --- | --- | --- |
| `a`, `b`, `old` | `ℚ` | 固定网格端点与根 old；积分要求 `0 < a < b` 和 `0 < old` |
| `m` | `ℕ` | 沿用既有 `m + 1` 网格约定 |
| `cells3` | `Finset (Fin 3 → Fin (m + 1))` | 第三层选中 owner 集 |
| `cap3` | `(Fin 3 → Fin (m + 1)) → ℚ` | 第三层存储的新 cap，仅在选中格使用 |
| `cells4` | `Finset (Fin 4 → Fin (m + 1))` | 第四层选中 owner 集 |
| `cap4` | `(Fin 4 → Fin (m + 1)) → ℚ` | 第四层存储的新 cap |
| `cells5` | `Finset (Fin 5 → Fin (m + 1))` | 第五层选中 owner 集 |
| `cap5` | `(Fin 5 → Fin (m + 1)) → ℚ` | 第五层存储的新 cap |

实际处理 tuple 为 `p : Fin 5 → ℕ`，顺序是 `p 0 > p 1 > p 2 > p 3 > p 4`。树内部历史是反向存储的 `[p 4, p 3, p 2, p 1, p 0]`。`primeHistoryTuple` 恢复处理顺序；第三祖先为 `[p 2, p 1, p 0]`，第四祖先为 `[p 3, p 2, p 1, p 0]`。

`historicalPrefixProject (by omega : r ≤ k)` 取处理 tuple 的前 `r` 个坐标。同一个操作用于投影 owner 标签；不重新排序网格坐标，也不从历史列表的最前端截取祖先。

每个 owner 使用原 `logPrimeMeshCell`，即逐坐标左闭右开的 `Ico`。唯一归属由既有 `logPrimeMeshCell_unique` 证明。内部网格墙沿用这一归属，不能先删去墙上真实素数再重建分区。

## 2. 有效 old 必须包含逐层 fallback

在同一共同网格上，Lean 定义严格遵循：

```text
cell3(j3) = if j3 ∈ cells3 then cap3(j3) else old
old4(j4)  = cell3(project3(j4))
cell4(j4) = if j4 ∈ cells4 then cap4(j4) else old4(j4)
old5(j5)  = cell4(project4(j5))
cell5(j5) = if j5 ∈ cells5 then cap5(j5) else old5(j5)
```

实坐标上的 `exponent3 / exponent4 / exponent5` 使用同一有限 Ico lookup；盒外分别回退到根 old、有效第三祖先、有效第四祖先。实际 level 为对应指数的 `N ^ exponent`。在未选中的第五格，两个实际第五 residual 在归一化以前就相等；所有选中第五格之外亦如此。

Part 2 的第四、第五层证书必须分别绑定 `D.old4 j` 和 `D.old5 j`。用根 `D.old` 替换已经升高的有效 old，不能供应实际继承许可。

## 3. 有限检查的准确边界

`D.levelCheck = true` 给出且仅给出三组有限比较：

```lean
(∀ j ∈ D.cells3, D.old ≤ D.cap3 j) ∧
  (∀ j ∈ D.cells4, D.old4 j ≤ D.cap4 j) ∧
  (∀ j ∈ D.cells5, D.old5 j ≤ D.cap5 j)
```

它在实际历史长度下推出祖先 level 的相应比较，并供应实际第四 policy 减第五 policy 的有限恒等式。它没有声称整盒 envelope、平方支持或最后的 `K/c` 界成立。

既有 `levelCheck_of_selectedBoxCapChecks` 接受 midpoint cap 的整盒检查及 cap 相等证明。独立模块 `StoredHistoricalBoxPermit` 另允许 Part 2 直接检查实际存储 cap，供应 old/new 严格比较、整盒 prefix-square 和 selected-subproduct-square 条件以及 envelope 上界。接入该通用 permit 时，证书仍须把其 `old j`、`cap j`、selected mask 和 envelope 参数识别成当前真实历史数据；通用 checker 本身不完成这种采用表识别。

## 4. 第五层共同区域、残差和积分

对第五格 `j`，令 `j3`、`j4` 为上述固定坐标投影。共同 parent 区域为

\[
R_j=C_j\cap\{t_0>t_1>t_2>t_3>t_4,\quad
3t_0<D.old,\quad t_0+t_1+3t_2<D.cell3(j3)\}.
\]

第五 candidate 来自实际第三 cap policy 的 rank-four frontier。第四层供应旧第五残差水平 `D.old5 j = D.cell4(j4)`，不增加一个 candidate filter。两个第五 own-cube 检查分别放在各自的 residual 里。

令 `G_lambda = primeOwnCubeGatedProfile lambda`。实际自然数 tuple 的每项均保留

\[
P=\prod_{i=0}^{4}p_i,\qquad Pp_4^2<N^\lambda,
\]

以及真实商水平 `N^lambda / P`。严格对数门为 `sum t + 2*t 4 < lambda`，分别应用于 `lambda = D.cap5 j` 和 `lambda = D.old5 j`。

`D.fifthCorrectionIntegral` 是以下真实 Lebesgue 积分的有限和：

\[
\sum_{j\in D.cells5}\int_{R_j}
\bigl(G_{D.cap5(j)}(t)-G_{D.old5(j)}(t)\bigr)
\prod_{i=0}^{4}\frac1{t_i}\,dt.
\]

`D.fifthPrimeCorrection` 已含 `log N / singularSeries N` 的 residual 归一化；不应再给它乘第二次该因子。literal `actualHistoricalFifthSaving` 以及实际 policy 密度差在转换时只乘一次。方向为 `upperFourth - upperFifth`，对应上述 `new residual - old residual`。

真实 prime carrier 始终含 `Nat.Prime p`、`¬p ∣ N`、`p < cap` 和原严格实上端点。finite reindex 保留 reciprocal-prime mass `prod_i 1/(p_i-1)` 与完整 parent validity。

## 5. 截断和边界接入

同一 `cap` 下，将外层 rough cutoff 从 `N^b` 提高到任意 `z ≥ N^b`，不改变完整归一化第五 saving。固定 owner 内每个实际素数严格小于 `N^b`；选中 owner 外 residual 差在归一化前已精确为零。本轮公开的 cutoff 恒等式保留 `log N / singularSeries N` 因子，包含墙上实际素数，不用零测论证，也不要求 `cap ≥ z`。

真实积分极限另要求 `cap(N) ≥ N^b` 最终成立，以完整覆盖选中 prime box 以及 residual 的素数 cutoff。cap 不必覆盖商水平 `N^lambda / P`。因此 moving `z(N)` 的接口要求两条独立的最终条件：`N^b ≤ cap(N)` 与 `N^b ≤ z(N)`；同一固定 `D` 不随 `N` 改变。literal `ceil(N^b)` 已有覆盖证明。

当前公式没有估计不足的 cap、降低到 `z < N^b`、裸 `floor(N^b)`、移动网格或随 `N` 变化的 `a,b` 所丢失的项。若改变 residual cap，需要另证同一 residual 或其误差，不能从外层 cutoff 不变性推出。

离散边界先由逐点 ramp 不等式乘真实非负 prime weight 后求和控制；连续零测墙只用于连续积分及其 ramp 极限。详细供应链、原端点与 `p∤N` 误差，以及源码中积分重写与有限加权估计的实际位置，见 [MATHEMATICAL_AUDIT.md](MATHEMATICAL_AUDIT.md)。这条链给出本固定有限族的渐近误差趋零，不给出手稿全部边界项的有效数值账。

## 6. 下游接收和仍缺输入

| 接收 Part | 可接收的接口 | 尚须供应的实际输入或证明 |
| --- | --- | --- |
| Part 0 | 四个本轮生产模块；针对当前根的导入补丁和逐模块验证记录；permit 已在 d036 接收 | 历史四模块的公共根集成及其规范门；将最终状态写入公共手稿映射。P1 没有修改这些公共文件 |
| Part 2 | `HistoricalPrefixCapData`、有效历史 old、Ico owner、独立 old/new cube 及真实 integral 的准确形状 | 手稿实际采用的 `cells3/4/5` 与 `cap3/4/5`；有效 old 的逐行绑定；有限 level 与 stored whole-box 检查；该实际共同区域的积分证书及不重计并域身份 |
| Part 3 | 精确实际 parent、所有第五候选、自然数 product 与同一 cap 下的 cutoff 不变性；已验证通用整盒 permit | P1 仍须补齐完整采用 policy 的支持及因子分解所需结构，并接上完整 modulus 与所选 subproduct 的实际许可识别 |
| Part 4 | 普通 lower-fourth 真实积分旧里程碑；本轮完整 inherited fifth saving 和第四减第五实际密度差的积分 | P1 的其余实际历史积分与完整采用上/下组合仍待补齐；其后接入 Part 2 数值证书与 Part 4 same-weight 密度界 |
| Part 5 | 原 `p∤N` carrier、严格端点、实际有符号有限组合和本固定族的边界趋零 | 同一实际系数的物理分布估计、全局边界/截断账与最终 counting 输入 |

P2 当前新增交接头为 `101bb2291cd51f9717544ce477122fdd44eda44d`，该增量只有文档；其 paired E0 `[0,64)` 积分认证不是上述历史第五采用表。`exact_Z` 仍是 paired fibre cutoff，不能充当历史 cap。独立 reported inherited-fifth 候选仍为 `SOURCE_PENDING`；本轮源码与验证不替它补造来源。

Part 0 的发布前新头为 `d0366ce64272e81faf6166a8a90050f56b328d38`，已经接收 `StoredHistoricalBoxPermit` 的 14 项生产声明并导入根；详见 [FINAL_P0_INTAKE.md](FINAL_P0_INTAKE.md)。当前应使用 `PART0_D036_HISTORY_IMPORT.patch` 接入本轮四个历史生产模块。Geometry 和 CellIntegral 已存在于 P1 的父头 `744316efd1887f21c91dd4b63c218fa27704c931`，而新 P0 头仍只保存它们的旧候选快照；本轮增量中 geometry 只有证明修复、cell 文件没有源码变动。单独 cherry-pick 本轮增量而不接收这两个父头生产文件，不足以应用全部导入。补丁的 `git apply --check` 成功仅证明固定根文件上的文本适用性，不证明接收分支已拥有各叶文件或已完成集成编译。

本轮结果不自动给出任一完整 upper density 的单独极限，也不完成所有已采用层的组合积分或最终 `K/c`。这些界没有被写进新的合法性前提。

这是一个可接收的历史积分及截断里程碑。P1 的后续责任仍包括：将全部实际采用层连成上/下 policy 的完整组合公式，补齐下游支持及因子分解所需的历史许可结构，以及完整构造的截断、回退和边界账。Part 2 供应实际固定选盒数据及有限合法性证书；本交接没有把上述尚未完成的 P1 工作转交给接收 Part。
