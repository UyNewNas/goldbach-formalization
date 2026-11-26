# Actual singleton 的固定 rectangle 尺度

状态：**SOURCE ONLY；未 elaboration、未编译、未核验 kernel，formal credit = 0。** 本目录只增加两个新 owner 的候选源码、一个旧 provider 的互补 postimage 和来源记录；不改变 canonical、原归档或现有执行入口。

本轮补齐从一个真实活 tuple 到固定 rectangle 尺度的有限几何连接。尺度由全部原 block 的下端决定：

\[
X_0=\prod_a\operatorname{lower}(b_a)=MUV,
\qquad M=\prod_{a\ne i,k}\operatorname{lower}(b_a).
\]

`X0` 不依赖 rectangle 中的 tuple、短积 `m`、模数 `q`、系数 `rho` 或 Fourier 模式 `xi`。原 Dictionary 选出的两个 occurrence 位置 `i,k` 作为输入保留，后续随 `m,q` 变化时不重新选择。

## 两个新声明

| 声明 | 已写出的合同 | 复用的原证明 |
| --- | --- | --- |
| `fixed_rectangle_fibre_window` | 全 rectangle 的乘积在 `[X0, 2^r X0]`；每个原 `shortSupport` 中的 `m` 满足 `M ≤ m ≤ 2^s M`；对原两个 long block 中任意 `u,v`，`muv` 仍在同一窗口 | `shortProduct_window`、`product_two_positions`、`short_card`、`owns_bounds` |
| `eventually_actual_singleton_fixed_rectangle_level` | 在真实 `scalarProfile` 非零点上取得 `N^(1-kap0)/64 < X0 ≤ 2N`，由原通用 threshold 推出 `1 < X0`、`X0/2 ≤ N ≤ X0^(1+kappa)`；同一 historical `Q` 中所有 `q` 满足 `q < X0^(1199/2000)` 及对应自然数 floor 界 | 原 `scalarProfile_complete_support`、`exists_manuscript_restrictedResidueScale_threshold`，后者只实例化 `c=1/64, C=2` |

`j ∈ range 3` 给出 `r=2(j+1)≤6`，因此 `2^r≤64`；原 `s+2=r` 给出 `s≤4` 和 `2^s≤16`。这些是原索引 carrier 上的计算：unit 位不删除，重复整数不按值去重，短积碰撞仍由原 `shortSupport` 保留。

只有一个实际点需要 `scalarProfile ≠ 0`。它支付物理 `N` 与固定 `X0` 的比较；其他 rectangle 点及每个固定 `m` fibre 的完整乘积支持由原 dyadic 窗口支付。声明没有从一个活点推出整 rectangle 活跃，也没有假设聚合 `blockCoefficient ≠ 0`、目标误差界或待证 local-level 界。

参数顺序为：先固定 `kappa, kap0, zeta` 及

\[
0<\kappa,\quad \kappa\le\zeta/10000,\quad
\zeta\le1/400,\quad \kappa_0<\kappa/(4(1+\kappa)),
\]

然后取 eventual `N`，再量化 `kap<1`、`B,cj,j,bs,ns,i,k` 和所有历史系数参数。模数集合保留原表达式

```lean
remainingModuli levelB N (trueDDeltaSupport old fresh N cap w z)
```

它就是现有 `historicalModuli` 的定义体。原 filter 中 `q<N^.599` 经原 threshold 的 `N≤X0^(1+kappa)` 及数值余量运输到 `.5995=1199/2000`；`Nat.le_floor` 随后给出整数界。`rho` 不参与尺度证明，原 signed kernel、coprime mean 和整数 `N` 均未替换。

前一个实际 tuple Dictionary 提供同一 `ns,bs,i,k` 和 rectangle membership；LogNormalization/LongComplement 提供同一完整乘积的 `scalarProfile ≠ 0`。本声明对任何满足这些原始条件的固定不同位置成立，未重复 long-role 分类，也未声称完整 P2 误差已闭合。

## 原声明的唯一 owner 与原子采用约束

来源锚为 `545566753bae9464560a871bea87ea663f90aa53`。旧 PhysicalLevel：

```text
docs/source-only/20261126/p1-singleton-physical-level/P1OriginalSingletonPhysicalLevel.lean
7957 B / SHA256 9b2986d114f8a05db3eba003b619ad5dfea729ef516d84d420ecd9a83b8f09b9
```

其 UTF-8 `[1738,2568)` 的 830 B 原块逐字提取到 `P1OriginalSingletonPhysicalSupport.lean`，包括原注释、statement 和 proof；块 SHA256 为 `857387a25bd5ba76e089441265e17ccd689a2f09cc870a69c3d9a1fa8ddf38ef`。声明仍名为

```lean
ImbalancedChen.P1OriginalSingletonPhysicalLevel.scalarProfile_complete_support
```

未来采用时必须一起选择 **新 PhysicalSupport owner + `provider-postimages/P1OriginalSingletonPhysicalLevel.lean`**。互补 postimage 只在原文件开头加 shared-owner import，并删除该精确原块，其余字节不变。不得同时编译 shared owner 与仍定义同名声明的未迁移 PhysicalLevel。

`LogNormalization` 与 `LongComplement` 原字节保持。前者仍 import PhysicalLevel，后者仍 import LogNormalization，因此原 local-level API 的传递导入不丢失。新 FixedRectangle 直接 import PhysicalSupport。当前旧 provider 文件没有被修改。

| 新源码或互补版本 | 字节数 | SHA256 |
| --- | ---: | --- |
| `P1OriginalSingletonFixedRectangleScale.lean` | 10204 | `431ad6ffb5b3561c877abb8ae978a7c47d7344d75fde8f9b2b62111aa19e7d04` |
| `P1OriginalSingletonPhysicalSupport.lean` | 1558 | `151fa7f863423bbf495e544f1c58cf7a6f94bf06194684b35620779013386723` |
| `provider-postimages/P1OriginalSingletonPhysicalLevel.lean` | 7184 | `9404ab156a719367f1b94efbcb477db2423b278b5f9125ca86be9ffdb75159e6` |

## 原稿与精确来源

固定稿件为 `UyNewNas/chen-imbalanced-semiprimes@a988cba584d803ae2856a0de50efb582f4f3dd6a` 的 `paper/release-20261106/en/coefficient-appendix.tex`，blob `10f3e2efb2074a9b97148a5151956e1d450be13f`，完整 39389 B / SHA256 `267af54481f344e806d4cb3ad602aa7f32020b930845e2aa152b7daaa2f9a440`。本轮复用已有缓存，未重新获取。

对应行段：251–270 为参数次序；535–548 为 units、原 physical chart 与完整乘积；621–630 为两长和短补积；751–763 为固定 `m`、`x≈MUV` 及 residue/divisor 变化；811–850 为后续指数预算和 individual sharp intervals。逐段字节区间、哈希和 API locator 保存在 `SOURCE_REVIEW.json`；提取与互补版本的可重建操作保存在 `EXTRACTION_BINDING.json`。

## 可复用边界及下一步

本目录不导入 HistoricalTwoLongP2、完整 PhysicalLevel 或缺失的 FixedM 链来取得 support。一次有界 import 核对仍发现继承的七个已登记 Fourier/selector 缺源，因此**不声明传递源码闭包已齐**；未再次搜寻或重建这些 owner。

下一步已有可复用来源，无需重写：

1. `P4BOriginalSharpNativeRow.sharp_fibre_identity` 是 generic 的原 sharp-profile/rough-fibre 恒等式，保持固定 `m,N,q,alpha` 和精确 mean。其完整旧导入仍触及已登记 FixedM 缺源；本轮没有复制或重证它。
2. HistoricalTwoLongP2 已有 `historical_rowCore_bound_at_physical_level`，其有限 core 使用物理 `.599` endpoint，未要求额外 `hlevel`。已提取的 36 条 rough/Brun/mean 声明和其来源边界保持原记录；未将提取等同于完整 E3 装配。
3. 后续短积大小、Brun order/cutoff 与固定 `X0` 仍须真实常数运输。从活 chart 和本窗口直接取得的是 `R_cj≤128X0`、`X0≤2R_cj`；旧 `eventually_short_transport` / `eventually_chart_brun` 要求的 `X≤16x` 不能直接改写为对 `X0` 已成立。固定 `K` 的 Brun 阈值次序也须保留。

因此，本轮完成的是固定全 rectangle 尺度和同原模数集合的 level 连接。尚未完成 sharp endpoint strips、rough-to-upper 误差、短积加权 E3、Fourier 重构或外层 Atlas 预算。已有 FixedM source stop 属于源码不可用；本次未发现稿内推导矛盾或反例。

## 核验范围

静态核验包括来源 pin、两新声明区间、830 B 原块与互补版本的逐字节恒等、保留消费者原字节、UTF-8/LF 与禁用 proof token 检查。独立只读审查的范围和结论单独记入 `SOURCE_REVIEW.json`。以上均不提供 Lean 编译、kernel 或 formal acceptance；未运行云任务、未改旧源、未 stage 或提交 Git。
