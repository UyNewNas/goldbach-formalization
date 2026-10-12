# P2 前 64 格：可读完整接口与 producer 原文来源

## 验证身份

这里提取的是已接受 P2 producer 的五个真实接口：生产证明源码提交 `f0c00f9ccce98e04af439321a92eb9fd0dd26203`，固定交接 `101bb2291cd51f9717544ce477122fdd44eda44d`。对应已实际成功的 P2 专项 CI 为源码 `e6d6d57323cc358cef060fb243ec386c13cb662d`、run `38252572597`、job `114822365913`、artifact `11749278994`。

**本提取没有读取或预认 `d0366ce64272e81faf6166a8a90050f56b328d38` 的新 core 完整类型。** 编制时 root 告知该 core 的 full build 与四个显式 target 已通过，后续 replay／类型导出仍由 root 接收；这里的编译器类型来源始终是已接受的 P2 producer 与其专项 CI。

目标声明实际归属模块是 `ImbalancedChen.Certificates.PairedV2Prefix64`，namespace 是 `ImbalancedChen.Certificates.PairedV2.Prefix64`。下面使用实际名称，没有创建 `pairedV2Prefix64_*` 别名。

### 三种文本的区别

| 文件／字段 | 身份 |
| --- | --- |
| 本文的五个 Lean 陈述头、`EXACT_SOURCE_STATEMENTS.json` | 固定源文件的完整可读声明头；用于明确显示 `Fin 4/60/64` 等参数，不冒充编译器原文 |
| `ACTUAL_PRODUCER_COMPLETE_RECORDS.json` 的 `type` 字段、`actual-producer-ppall/*.txt`、`COMPLETE_PRODUCER_PP_ALL.md` | 实际编译器完整 `pp.all` 原文，所有参数、实例、宇宙与 coercion 均保留 |
| 同一原始记录的 `readable_type` 字段 | producer 另外打印的原始可读类型；该 pretty printer 有些索引类型通过上下文推断，因此本文同时列出源码中的显式参数 |

五个原始记录已逐项比对 producer `compiler-types.json`、producer 原始 audit log、实际 P2 CI `declarations.json`、CI 原始 `axioms.log` 以及先前接收的类型摘录，内容相同。每份 `.txt` 直接写入相应 `type` 字段的 UTF-8 字节，没有添换行。`original-log-lines/` 保留原始 marker 行；原日志行号、字节位置及散列在 `PROVENANCE.json` 中。

本次只执行既有文件的提取、字节比对和来源记录，没有运行 Lean、内核 checker、公理审计、CI、网络或证明重跑。

## 五个完整可读陈述

以下声明头均来自 namespace `ImbalancedChen.Certificates.PairedV2.Prefix64`；证明体保留在附带的原始源文件中。除 `source_ordinal_coverage` 的 `n : ℕ` 外，这些 theorem 没有额外显式输入参数，也没有 `hLower`、`hUpper` 或解析 `K` 密度证明作为假设。它们仍只陈述下面明确定义的有限数值积分对象。

### 1. 真实积分语义

全名：`ImbalancedChen.Certificates.PairedV2.Prefix64.integral_semantics`。

```lean
theorem integral_semantics :
    integral = ((K : ℝ) / 80) * ∑ i : Fin 64,
      ∫ t in (tLower (rowIndices i).1 : ℝ)..(tUpper (rowIndices i).1 : ℝ),
      ∫ u in (uLower (rowIndices i).2 : ℝ)..(uUpper (rowIndices i).2 : ℝ),
      ∫ z in (a : ℝ)..(rowZ i : ℝ), ∫ w in (a : ℝ)..z,
        1 / (t * u * z ^ 2 * w)
```

这里 `i` 遍历全部 `Fin 64`；`t,u,z,w` 均为实数，四个 `intervalIntegral` 使用实数上的 volume 测度。上、下限是下面给出的精确有理数经实数 coercion 得到。它是有限和的真实积分恒等式，不是数值近似公式。

### 2. 已证明的双边数值界

全名：`ImbalancedChen.Certificates.PairedV2.Prefix64.integral_bounds`。

```lean
theorem integral_bounds :
    (lowerBound : ℝ) ≤ integral ∧ integral ≤ (upperBound : ℝ)
```

代入源码的精确有理数后，界为：

\[
\frac{203256527543633}{10^{20}}
\le \mathrm{Prefix64.integral}\le
\frac{203256645234388}{10^{20}}.
\]

源码中的上界写成约分形式 `50814161308597 / 25000000000000000000`，与上式严格相等。

### 3. 原四格与新增六十格的真实积分追加关系

全名：`ImbalancedChen.Certificates.PairedV2.Prefix64.integral_eq_parts`。

```lean
theorem integral_eq_parts :
    integral = Prefix4.integral + Batch4To64.integral
```

这两个输入分别对 `Fin 4` 和 `Fin 60` 求和，追加后的对象对 `Fin 64` 求和。源码通过真实 `rowIntegral` 的 `Fin.sum_univ_add` 分解证明本式，再将两个已证明的区间相加。旧四格只出现一次，没有另外把首格重新加入。

### 4. 原始行号的准确覆盖

全名：`ImbalancedChen.Certificates.PairedV2.Prefix64.source_ordinal_coverage`。

```lean
theorem source_ordinal_coverage (n : ℕ) :
    ((∃ i : Fin 4, Prefix4.rowOrdinal i = n) ∨
      (∃ i : Fin 60, Batch4To64.rowOrdinal i = n)) ↔ n < 64
```

这是对每个自然数 `n` 的双向命题：旧批或新批中出现的原始行号，恰好为 `0≤n<64`。其两段不交还由同一源码的 `source_ranges_disjoint` 单独陈述；该覆盖定理本身没有声称完整 17572 行均已覆盖。

### 5. 实际网格坐标不重复

全名：`ImbalancedChen.Certificates.PairedV2.Prefix64.rowIndices_injective`。

```lean
theorem rowIndices_injective : Function.Injective rowIndices
```

`rowIndices` 的完整类型是 `Fin 64 → ℕ × ℕ`。按 `Function.Injective` 的含义，任意 `i,j : Fin 64`，若实际网格坐标对 `rowIndices i = rowIndices j`，则 `i=j`。这独立于原始行号覆盖；源码通过实际整数键的 63 个相邻严格不等式得到单射，没有把“行号不同”当作“坐标不同”的假设。

## 所有参数、常数及数据定义

### 公共有理常数与网格

这些实际定义位于 namespace `ImbalancedChen.Certificates.PairedV2` 的 `PairedV2Data.lean`：

```lean
def a : ℚ := 417 / 5000
def h : ℚ := 19 / 125
def d : ℚ := 59 / 250
def mu : ℚ := 25 / 128
def K : ℚ := 8452171 / 1250000

def tLower (i : ℕ) : ℚ := mu + (d - mu) * i / 512
def tUpper (i : ℕ) : ℚ := mu + (d - mu) * (i + 1) / 512
def uLower (j : ℕ) : ℚ := a + (h - a) * j / 512
def uUpper (j : ℕ) : ℚ := a + (h - a) * (j + 1) / 512
```

`d` 在此处是上述固定有理数，索引以自然数进入两个 512 等分网格。没有新增自由实参数或变动端点。

### 真实四重积分的定义

在 namespace `ImbalancedChen.Certificates` 的 `PairedFibreIntegral.lean`：

```lean
def pairedFibreKernel (t u z w : ℝ) : ℝ :=
  (1 / t) * ((1 / u) * ((1 / z ^ 2) * (1 / w)))

def pairedLocalIntegral (K a tl tr ul ur Z : ℝ) : ℝ :=
  (K / 80) * ∫ t in tl..tr, ∫ u in ul..ur,
    ∫ z in a..Z, ∫ w in a..z, pairedFibreKernel t u z w
```

因此系数始终为一次 `K/80`。它没有在 `Prefix64.integral_semantics` 中再次乘入一个额外归一化因子。

### 旧四格、新六十格与累计对象

在 `Prefix4` namespace：

```lean
def rowOrdinal (i : Fin 4) : ℕ := i.val
noncomputable def integral : ℝ := ∑ i : Fin 4, rowIntegral i
```

在 `Batch4To64` namespace：

```lean
def rowOrdinal (i : Fin 60) : ℕ := 4 + i.val
noncomputable def integral : ℝ := ∑ i : Fin 60, rowIntegral i
```

两者的 `rowIntegral` 均使用本批自己的 `rowIndices`、`rowZ`，代入相同的 `pairedLocalIntegral`、公共常数和网格函数。每行精确坐标与 `rowZ` 有理数已完整提取到 `ROWS_0_63_SOURCE_VALUES.json`；其 64 条数据分别来自未改写的 `PairedV2Prefix4Data.lean` 和 `PairedV2Batch4To64Data.lean`。完整源数据文件也附在 `fixed-source/`，没有以省略号代替未列数据。

累计 `Prefix64` namespace 的定义如下：

```lean
def prefixIndex (i : Fin 4) : Fin 64 := Fin.castAdd 60 i
def batchIndex (i : Fin 60) : Fin 64 := Fin.natAdd 4 i

def rowIndices : Fin 64 → ℕ × ℕ :=
  Fin.append Prefix4.rowIndices Batch4To64.rowIndices

def rowZ : Fin 64 → ℚ :=
  Fin.append Prefix4.rowZ Batch4To64.rowZ

def rowOrdinal : Fin 64 → ℕ :=
  Fin.append Prefix4.rowOrdinal Batch4To64.rowOrdinal

noncomputable def rowIntegral (i : Fin 64) : ℝ :=
  pairedLocalIntegral (K : ℝ) a (tLower (rowIndices i).1)
    (tUpper (rowIndices i).1) (uLower (rowIndices i).2)
    (uUpper (rowIndices i).2) (rowZ i)

noncomputable def integral : ℝ := ∑ i : Fin 64, rowIntegral i

def lowerBound : ℚ := 203256527543633 / 100000000000000000000
def upperBound : ℚ := 50814161308597 / 25000000000000000000
```

### 三个区间的准确常数

下表为统一分母显示；原代码中的约分形式同时保留。

| 对象 | 原始零基行号 | 下界 `/10^20` | 上界 `/10^20` |
| --- | --- | --- | --- |
| `Prefix4.integral` | `[0,4)` | `12676565261567` | `12676572571081` |
| `Batch4To64.integral` | `[4,64)` | `190579962282066` | `190580072663307` |
| `Prefix64.integral` | `[0,64)` | `203256527543633` | `203256645234388` |

`Batch4To64.lowerBound` 的实际源码为 `95289981141033 / 50000000000000000000`。表中其余旧四格和新批上界直接使用 `/100000000000000000000`；累计上界采用前述约分式。

## 完整 pp.all 原文与来源散列

五项完整原文另见 `COMPLETE_PRODUCER_PP_ALL.md`，未以可读重述替换。逐项 `type` 字段的 UTF-8 散列如下：

| 短名 | 字节数 | SHA-256 |
| --- | ---: | --- |
| `integral_semantics` | 4792 | `68a4f4c2142258e10edce3068e0089f5db16654d3e56a303d30101776e985166` |
| `integral_bounds` | 379 | `8bc7d0cc65a190283c3aa58bc609a297ca1f850e3b4207e7464e446f6a3a5e57` |
| `integral_eq_parts` | 256 | `11d44db197a95929e5af5beca5254a016fc2d9d9d001f1dfe85b931e060eb140` |
| `source_ordinal_coverage` | 647 | `96c8f524d71a0fc0a747a1b5b83de2e1f3daafe0c1b8b316ec1aac80a3493e09` |
| `rowIndices_injective` | 177 | `65e0bb67b146e40ab643a3e810ad73ef578ef2648a6b796fa5cceae186499d91` |

`source_ordinal_coverage` 的字符数为 645，UTF-8 字节数为 647；二者没有混用。它的实际传递公理是 `propext`、`Quot.sound`；其余四项为 `propext`、`Classical.choice`、`Quot.sound`。

关键原始来源：

| 原始文件 | SHA-256 |
| --- | --- |
| producer `compiler-types.json`，完整 709 条 | `882a111f3bbf5bdc902ffd00aa52565f99cccaa027f2ecb6ffd8075889925cd4` |
| P2 CI `declarations.json`，完整 709 条 | `882a111f3bbf5bdc902ffd00aa52565f99cccaa027f2ecb6ffd8075889925cd4` |
| producer `20261012T124344374925Z-compile-verification.part2.CertificateAudit.log` | `7433719877769f9fe95751fac6a3f8843cb27c69a798a2d38117342e53a06b7a` |
| P2 CI `axioms.log` | `1f1b4790f0320a9e4a716eee3833337e09a3ffe16ae78863c10f3a824a48579c` |
| P2 原始 CI ZIP | `4f0b9cc1232226392515eda5ccf880a40241cc5afc8d6defcbac45206089d663` |
| `PairedV2Prefix64.lean` 实际源码 | `11b0d1bf69c25abf05256eb0e6d52b2c743d37b47650a15ba6da90e2a453d7da` |

所有原始绝对路径、源码身份与 marker 行位置在 `PROVENANCE.json` 中完整保留。先前 `KEY_TYPES_SELECTION.md` 保持原件，散列仍为 `608add5fcccb3e38fe319616cd070f5f8cbf4fb05579708aac1ae7a36a998b60`。

## 数值证书的边界与待供应接口

采用版本仍是冻结手稿 `ba6ec11d800eccc54406490631895e174de85766` 的 **same-mask-v2**。原证书 JSON 的 SHA-256 为 `f6d31386f93cf77888ea4771ffa549a1cf61dca700bac618ff7646566a02f9b7`；本累计只含 E0 原始 `[0,64)` 行。

**这 64 格的双边界没有完成全 17572 行证书。** E0 的 `[64,6091)` 与 E1 的 `[6091,17572)` 尚不在本界内。原始 stored Q160 数值只作为来源记录，并未代替此次真实积分证明；完整 saved-floor 语义也没有由这五项定理闭合。

| 待交接内容 | 需要接收的真实供应 |
| --- | --- |
| 全采用 mask 与完整数值区间 | P2 剩余行及完整证书语义；有限 64 行覆盖不能改写成全 mask 覆盖 |
| 历史选择、parent 许可、合法支持与几何并域 | P1 的同一实际构造；网格坐标单射不直接等于完整历史／并域积分身份 |
| 实际权、计数到积分、余项拆分 | P1 的实际对象和身份桥，以及相应 P3／P4／P5 误差供应；不能把数值积分和直接命名为实际计数 |
| 同一实际 `rho` 的解析密度 | Part 4-A 的真实 `K` 密度证明；本文件中的有理常数 `K` 本身不是这种证明 |
| 完整上界和完整 Chen 均值下界 | Part 4-B 的 `hUpper`，Part 5 的真实 `c` 与 `hLower`；Part 5 只需等待 Part 4-A，无须等待 Part 4-B |

因此这些局部 theorem 可以是无外部假设的已证数值组件，同时最终手稿主定理仍须等待上述实际供应。本提取没有新增结构、类型类或假设包装来隐藏这些输入。
