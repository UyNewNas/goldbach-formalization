# P1 singleton：实际支撑到历史模数的局部 level

**SOURCE ONLY；未 elaboration、未编译、未 kernel 验收。**

新文件 [P1OriginalSingletonPhysicalLevel.lean](P1OriginalSingletonPhysicalLevel.lean)
把实际 singleton profile、原有序 HB tuple 和历史 true-d carrier 接到同一个完整局部尺度。
来源与静态审查见 [SOURCE_REVIEW.json](SOURCE_REVIEW.json)。原 canonical、归档、generic
scale 证明和 driver 均未修改；本目录代码尚未运行编译或内核检查。

## 已写出的实际证明

固定 `kappa > 0`、`kappa ≤ zeta/10000`、`zeta ≤ 1/400` 和
`kap0 < kappa/(4*(1+kappa))`。源码先取得一个 eventual `N` 门槛，然后才量化
profile 的 `kap/B`、chart、HB order、实际 tuple、所选 occurrence、whole-complement block、
`old/fresh`、历史系数参数及 `q`。

| 声明 | 证明内容 |
|---|---|
| `scalarProfile_complete_support` | 从真实 `scalarProfile kap B N cj kap0 n ≠ 0`、`kap < 1` 与 `N > 0`，调用原 `scalarProfile_eq_ambient` / `scalarProfile_support`，得到 `N^(1-kap0) < n ≤ 2N`。 |
| `eventually_actual_singleton_local_level` | 用真实单元组 `gs=[{integer:=n,row:=j,factors:=fs,mem:=hfs}]`，证明 `joined gs=fs`、`completeInteger gs=n`，再调用原 complete-scale threshold，最终得到实际历史 `q < x^(1199/2000)` 及自然数 floor 界。 |
| `eventually_actual_singleton_historical_rowCore_bound` | 将上述局部 endpoint 直接用于本轮已有 `historical_rowCore_bound`，支付其 `hlevel` 前提；保留原 `Q/rho/N` 及其他原有参数条件。 |

这里 `fs ∈ factorTuples (2*(j+1)) n`，`p ∈ fs`，`Owns b p`，
`Owns c (n/p)`，且

\[
x=\operatorname{localScale}(b,c)=\operatorname{lower}(b)\operatorname{lower}(c).
\]

`c` 对应所选 occurrence 的**全部补乘积**。因此 `x` 是完整乘积尺度；没有把
残余商 `n/p` 单独当作局部尺度。实际 profile 已支付 generic supplier 所需的 trim 和上界，
取其 `C=2` 后得到

\[
1<x,\qquad x/2\le N\le x^{1+\kappa}.
\]

原 `historicalModuli` 的定义仍是 `remainingModuli` 对同一个
`trueDDeltaSupport` 的过滤。它直接提供 `q < N^(599/1000)`，随后使用原 P4 中已有的
三步 rpow 运输方式：

\[
q<N^{599/1000}
\le (x^{1+\kappa})^{599/1000}
=x^{(1+\kappa)599/1000}
\le x^{1199/2000}.
\]

没有假设最终 trim、moving-residue 或 local-level 结论。`Nat.le_floor` 把最后的严格界
变为 `q ≤ ⌊x^(1199/2000)⌋₊`，供现有有限 P2 invoice 使用。

## 复用来源与数值核对

源码锚为 `f3084a33ca08daf305ddd7c6eb660a038794614a`。直接 imports 只有：

- `P5ActualLowerNormalizedAtlasOccurrence`：实际 scalar profile 与原支撑定理。
- `P5OriginalHBCompleteProductScale`：原 `OriginalGroupTuple`、`joined`、`completeInteger`、
  `localScale` 和 `exists_actual_HB_residue_threshold`。没有复制或重新证明其有限 tuple 几何。
- `P1OriginalHistoricalTwoLongP2`：本轮新 source-only 的同一历史 `Q/rho` 与有限 P2 估计。

`P4BOriginalHighRankLocalLevel` 只作为 rpow 证明步骤的来源核对，没有导入。
已检查的旧 singleton medium-window 源提供 `B=6` 的相关支撑几何；原 P4 local-level
源还有专用母 profile 和 coefficient-support 条件；新 P2 的旧 corollary 只给物理
`N^.599` floor。此次新增的是实际 singleton tuple 与历史 true-d carrier 的局部 `x` 绑定，
没有据这组有界检查断言其他历史来源全局不存在，也没有重搜九份已登记缺源。

在最宽允许参数处，精确有理数核对为：

| 裕量 | 值 |
|---|---:|
| `1199/2000 - (1 + 1/4000000) * 599/1000` | `1999401/4000000000` |
| `3/5 - 1199/2000` | `1/2000` |
| `1 - 20/400 - 1199/2000` | `701/2000` |
| `1 - 40/400 - 3*(1199/2000)/2` | `3/4000` |

通用数值裕量已由既有 `P4BOriginalHighRankLocalLevel.typeI_margins` 提供，本文件删除了不必要的重复声明。上表仅作选参数的算术核对。主代理已独立核对实际支撑、完整尺度、原模数过滤和 P2 调用；这些核对不是 Lean 验收。

固定 1106
[coefficient appendix](https://github.com/UyNewNas/chen-imbalanced-semiprimes/blob/a988cba584d803ae2856a0de50efb582f4f3dd6a/paper/release-20261106/en/coefficient-appendix.tex)
的 252–271 行给出参数选择顺序和 `.599` 到局部 `<3/5` 的要求；507–548 行给出实际
trim、HB 与完整尺度；803–820 行给出 one-long / two-long 误差所需的局部 level 和裕量。
本文复用了共享的同一稿件缓存。

## 保留边界

本轮没有声称实际两长字典已经与最后的 P2 corollary 完整闭合。仍需在所需的
fibre/rectangle 范围内，把真实两长选择接到这里的 `p` 和 whole-complement block，
并将 P2 的短位载体与真实 `ShortPositions` 对齐。corollary 保留原 short-block 几何、
Brun、Mellin 等条件，不能据其存在跳过这些连接。

Closed-block Fourier 复原、rough-to-Brun、individual endpoint strips、E1/E3/E4 以及
完整外层预算仍是后续义务。三个直接 supplier 中有 source-only 路径；本目录没有安装
canonical 路由，也没有宣称完整递归源码或对象闭包已就绪。
