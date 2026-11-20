# P4 actual-row 四源增量独审

**裁定：AL，仅限原两母 live no-medium 行到 literal smooth-Brun polynomialRow 的 E4 展开核心付款。** 新终端 `eventually_actual_pair_assignment` 的实际行来源、尺度条件与统一阈值均有源码供给；没有发现目标形假设替代证明或实质数学缺口。**未编译/未 kernel 验收；完整 rough no-medium、母积分与 hUpper 仍 HOLD。**

本次只审新四源，不重证、不重签旧三核。旧独审 `n11-p4-branch-review` 与作者全部文件保持不变。只进行了 source/JSON/hash/词法核验；未运行 Lean/Lake/LSP/kernel/helper/fixture/stage/setup/guard，未加载对象、下载、操作 Git/GitHub/CI/额度或派发子任务。

## 1. 固定对象

新 freeze：`revision-actual-row/FREEZE.json`，SHA256 `fbcb94463a029b85d7c6ed9cb0cf7a5b07ef26b03ec57f17e44083363a474870`。

SOURCE_RECEIPT：`a86c315795d9d57d67debfcfe7ec7eacee67d6cd8ce80a4025039d93a34a656a`。36 个 source pins（4 新源、27 reused、5 immutable parent）及 7 个包内文件 bytes/hash 全匹配；29 个公开声明的行号和首行前缀匹配。终端完整源码类型为 Assignment 38–87，词法 SHA256 `4bf37ade94e4dbdbe3d40e6feed3602f23e7d8042da4424c909a20aa5a1cebb6`；提取时保留类型内全部 `let :=`，只在声明末尾 `:= by` 截断。无 elaborated type/Lean AST 声称。

新四源：

| 简称 | SHA256 |
|---|---|
| Rows = P4BOriginalNoMediumPairRows | e08915d8c52725b1195069a0822a6e95239d89daceebe4e33a288d9ca679627c |
| Scales = P4BOriginalTwoLongActualScales | e43733cc2d49effd2c2f4d48c195b8c8ffdd67dc2f4cd5d6893c663d35d2fe3c |
| Dictionary = P4BOriginalTwoLongActualDictionary | 0a8f213e63afc934afd1afa4aa8eaeeb850d5298201ec3db2a4232623ff69b33 |
| Assignment = P4BOriginalTwoLongActualAssignment | 54b9a75f977dbebca95a709710cae3483ab58e24c7c9fd62321b6722a8def13f |

## 2. 真正的行与死行

Rows 105–109 的 `live` 是原整数矩形上存在 `hbSlots * ofReal(integerProfile) ≠ 0`。Rows 111–135 逐离散源项证明 `rowAtom=0`，继而给 `rowAtom = if live then rowAtom else 0`。它删除的是原完整 signed discrepancy 中确为零的离散行，而不是宣布 Fourier amplitude 或单个 Mellin component 逐点为零。

没有从一个 tuple 的非零推断同乘积所有 tuple 的总 `blockCoefficient` 非零；后者可能有符号抵消。Rows 的新 `group_has_long` 167–185 直接使用该 tuple 的坐标上界、原 no-medium 测试和母乘积下界，避开了这一错误推断。

Rows 48–62 从原两个 Row records 的 `typeIValue` 定义抽出 selector。78–92 用旧 `blockWords_spec`/`ofFn_blockVector` 接真实 bank 词；64–76 的阈值与原 atlas 的 `X^(3ζ)`、`X^(1/3+ζ/4)` 相同。该选择仅依赖 block，不读 rho、频率、误差符号或整数 tuple。

## 3. 两长位置、真实 arity 与短积

真实旧 `P4BUpperPairOrderedRowModes.rowBank` 210–219 与 `modeBank` 277–294 枚举 j,l∈range 3，Fin.append 的完整维数为 `2(j+1)+2(l+1)≤12`。不是从新定理的假设猜出实际 HB rank。

Rows 189–220 调用原 `normalized_support` 取得两母乘积分别大于 `N^(19/96)`，并从两条 psi 窗得完整乘积 `<4X`。Rows 225–324 的逻辑为：

* 每母至多六槽。若全无 long，no-medium 使各 lower<A=X^(3ζ)，真实整数乘积≤64A⁶；Scales 141–161 在共同 N 阈值后证明 `64X^(18ζ)<N^(19/96)`，矛盾。
* 三 long 则 raw lower-product≥B³。真实 raw-product≤源 tuple 完整乘积<4X，而 B³=`X*X^(3ζ/4)`、4<X^(3ζ/4)，故原 `atMostTwoLong` 排除第三条。
* 每母 `chooseLong` 固定读本母的 blocks。`Fin.castAdd` 与 `Fin.natAdd` 给两个不同位置；`short_card` 对 occurrence 补集证明 `card+2=总维数`，故余下≤10。单位、重复 block、重复 role 和重复整数都没有按数值合并。
* `M=shortScale` 是剩余 block lower 的乘积；每个余下位置 lower<X^(3ζ)，得到 M≤X^(30ζ)。没有把短整数乘积的 dyadic owner 当成这个 M。

Rows 328–349 对同一非零 hbSlots 使用旧 `pair_mobius_cutoff`，保留两个原母各自的 hbCutoff。其与 Scales 106–124 的 cutoff≤B 结合，排除所选 long 为 Mobius；只保留 one/log。此处也不需要 blockCoefficient 非零。

## 4. 参数运输包含 M、y² 与真实 retained cube

Scales 83–104 用 X≤16x 将 M≤X^(30ζ) 送为 M≤x^(40ζ)，10ζ 支付固定 `16^(30ζ)`；同一阈值给全部短块 `2 lower≤x`。Assignment 139–150 从实际正 tuple 的乘积界统一得两长 `1≤U,V≤4x`。

Scales 36–81 保留原 Z=`beforeHBCutoff K [cj,ck]`，精确为 `roughF(2^(6K+2)*4X)`。X≤16x、x≤4X 与固定 K 的大阈值给实参 t∈[x,x²]；旧 `roughF_mono/roughF_upper` 给 roughZ(x)≤Z≤roughZ(x)²。再对 **eps/2** 调用实数版旧支撑引理，得到

`Z^(2*halfOrder x+1) ≤ supportSize(x)² ≤ x^eps`。

因此真实 prime alphabet 没变，增长 Brun order 未进入固定模数矩的阶数，也未漏掉 y²。eps=1/16000、theta=1199/2000、ζ≤1/400 给

`40ζ + 2eps + 3theta/2 ≤ 1599/1600 < 1`。

这是整个 `M*y²*D^(3/2)` 的固定 1/1600 power reserve，不仅是 M 的余量。

Assignment 122–126 用所选 long 与一个真实 source point 的互补 owner 构造原 fibre，借 `same_scale` 取得同一个 x 的 `eventually_live_level`。157–159 从同一 final rho 的原 `.599` hRange 得 active v<x^theta，再用整数性取 D=floor(x^theta)。没有把 presieve 的 omega、beta 或 ell 当作完整模数上界。

频率不是新增 hTwist 前提。Assignment 78、162–163 直接使用原 `outsideCube (H N A0)` 的补集；旧 `eventually_local_twists` 对任意维数、任意该 cube 的 xi 及每个坐标统一给 `(log x)^(bandwidthOrder A0+1)`。

取作尺度代表的 y 只用于选一个满足所有 scalar gates 的 x。估计仍覆盖原整个 signed shortSupport/Brun 源；没有把 row 的其它整数裁到 y 的 fibre，也没有按 rho 或 xi 选择 y。终端在 y、x、两长选择之后才量化 rho、S、xi，足以支持后续统一使用。

## 5. N 阈值顺序

Assignment 88–100 的顺序经逐句核查成立：

1. 固定 K、B、A0、A、ζ、κ、kap0，利用旧已付核心的统一 `∀ᶠ x`、short transport、实际 Brun 支撑与 smoothing schedule，取得 x0；另取 X0。
2. `eventually_live_large ht1 (max x0 X0)` 在 N 上统一运输阈值。它在固定 T 后量化任意合法 b/kap/s、行维数、cj/ck、blocks、source point 与选中坐标。
3. 同一 N filter 合并 mother short gap、live local level、retained frequency bound 和 N≥2。
4. 101 行之后才引入所有动态 row 数据；156 行之后才引入 policy/coefficient/S；161 行之后才引入所有 retained xi。

所以 N0 对随 N 扩大的原 rowBank、所有 legal width 及整个 H(N,A0) cube 是统一的。没有先固定行/频率取得阈值，再交换量词。global hRange 是旧 FineDensity 对既定同一族的 `.599` 支撑供给，而非误差上界或新 hAssigned/hGeometry oracle。

## 6. 同 Q/rho 字典与结论范围

Dictionary 25–80 调用的是通用 `rectangle_signed_pushforward`，外层 S/rho 任意；没有调用旧 `retained_mode_eq_fibres` 的 lowerQ/lowerRho 专用包装。实际引用的 lower-rectangle 与 upper ordered-rectangle 均定义为每位置 `.unit→{1}`、`.dyadic j→Ioc(2^j,2^(j+1))` 的 piFinset，scales 均为 lower；这里的载体匹配是实定义匹配，不是把两套物理系数视作相等。

`actual_pair_mode` 85–112 保留原 Fin.append、两母各自 cutoff、实际 rowRoles、occurrenceMode、完整整数乘积与同一原 P4 rho。所有按 short product 的碰撞仍是有符号有限 fibre 和。

`polynomialRow` 118–124 是真实长整数上的 `smoothBrunTupleCore` 源。129–141 逐原物理 v 使用已证明的 `smoothBrunTupleCore_eq_expansion`，仅有限交换 v/short 的求和。d1,d2 进入 short*d1*d2 及 U/d1、V/d2，原 v 与目标 N 未变；没有把原 v 的 squarefree 性转用于 c²d 或 vd1d2。

终端 164–168 通过该精确身份式消费旧 E4 核心，推出 literal polynomialRow 的任意固定对数精度界。此结论符合原稿 `coefficient-appendix.tex` 621–629、smooth-core 段及 799–817 的路线。

未发现需要 HOLD 的新数学错误。下列仍是本包以外的真实工作，AL 不覆盖：rough fibre 与 smooth polynomial 的 E1/E3 比较（尤其 E3 的两份 mean）、原 individual endpoint strips、完整 noMediumAtlas/bank 求和与母 amplitude 积分、log54/scalar/尾项恢复、原 H_N/hUpper。`actual_pair_mode` 和 `polynomialRow_eq_core` 是两个不同源的正确身份式，不是 rough=polynomial 的证明。冻结包也没有这样声称。

本增量 AL 仅是源码数学审查；精确传递依赖选择、Lean elaboration 与 kernel replay 均未执行，保持原审查与 source65 的验收边界。
