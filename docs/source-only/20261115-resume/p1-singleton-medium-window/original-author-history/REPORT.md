# P1 singleton first-medium: actual local window

本件补写原稿内一个必要的小叶：从 final singleton 的真实归一化 profile、原 first-medium 位置及完整补积 owner，推导整个活 fibre 的局部尺度与原 before-HB 截断。新增一份 Lean candidate；未运行 Lean、未编译、没有 kernel 验收。完整 singleton medium 付款、P1.4 与历史 middle HOLD 保持未闭。

原稿位置是 `chen-imbalanced-semiprimes` 已冻结文本 `proof-library/source/distribution-prime-product-completion-20261010.txt` L 97–117、173–175。L 107–117 将活 HB 矩形的完整补积 dyadic 化，要求同图截断比较及物理剩余范围；L 173–175 将原 medium 窗口换算到局部完整尺度。本件属于该处可补齐的省略推导，不是新分析定理，也没有发现这段原命题的反例。

## 新增声明与真实输入

`P1OriginalSingletonMediumWindow.lean` 的公开终端为 `eventually_original_medium_window`。固定 `K, xMin, kap, zeta, kappa, kap0` 后才给出一个关于物理 `N` 的 eventual threshold，随后量化所有 `cj, r, bs, i, C`。其输入仅为：

- `integerProfile kap 6 N cj kap0` 在 `fibre bs i C` 中确有非零点；
- 原 `firstMedium (originalMediumLow zeta [cj]) (originalMediumHigh zeta [cj]) (List.ofFn bs)` 选中位置 `i.val`；
- 原允许的固定参数约束：`kap<1`、`0<zeta≤1/400`、`kappa>0`、`kap0<kappa/(4*(1+kappa))` 及 `kap0<1`。

`kap` 是 actualLicence 的下边界/平滑参数，`kap0` 是完整乘积 smooth trim，`kappa` 是 M 的移动剩余幂余量。它们没有被错误合并。原真实调用还保留其正性、矩阶及更小的有限共同上界；本局部几何不放宽这些调用约束。`xMin` 是给下游已有 SW theorem 使用的固定局部下限，不是 profile 的 `B=6`。

设 `U=lower(bs i)`、`V=lower C`、`x=UV`、`X=R cj`、`v=2^(6*K+3)*X`。候选推导：

```text
N^(1-kap0)/4 ≤ x ≤ 2*N
X ≤ 8*x,                 x ≤ 2*X
xMin ≤ x, 1 < x
x/2 ≤ N ≤ x^(1+kappa),   x^(1-zeta) ≤ N
1 < U,                   x^(2*zeta) ≤ U ≤ x^(1/3+zeta/2)
2*U ≤ x
x ≤ v ≤ x²
roughF(x) ≤ beforeHBCutoff K [cj] = roughF(v)
          ≤ x^(2/(log(log x))³).
```

最关键的有限输入完全来自原源：

1. `integerProfile` 只是原 `scalarProfile` 在完整乘积上的值。`scalarProfile_eq_ambient` 分离同一 actualLicence 的归一化权、原 eta trim 和原 psi 母图；非零 eta 给出 `N^(1-kap0)<completeProduct`，`scalarProfile_support` 给出 `completeProduct≤2*N`。
2. 复用原 `tuple_scale` 得到 `x≤completeProduct≤4*x`；由同一个非零 psi 得到 `X/2<completeProduct<2*X`，故获得上述 `1/4,2,8,2` 常数。
3. `firstMedium_some` 给出同一个按位置选取的 `X^(3*zeta)≤U≤X^(1/3+zeta/4)`。严格的幂余量吸收固定常数。原 `RestrictedResidueScale` 给出共同的物理 N 阈值，原 `roughF_mono/roughF_upper` 比较同一个 `v`；没有把 `Zchart` 替换为 `roughF x`。
4. 复用 `same_scale` 将一个活点推出的结论传给整个 fibre。没有要求该 fibre 每个整数点的 profile 非零，也没有按模数或误差符号重新选位置/补积 owner。

虽然通用的 `tuple_scale`、`fibre` 位于 P4B 文件，它们的声明只量化任意槽数的整数矩形。本件没有调用那里的两母图 `live_geometry`，也没有以 `P4BUpperPairOrderedRowGeometry.integerProfile` 代替单组 profile。

## 同原最终调用的对应

原终端 `P1OriginalSingletonMiddleTensor.lean` L 130–146 保持不变：`L=actualLicence kap 6 P.N`，`S=products P`，`c(d)=(free P d:ℂ)`，prime cap 为 `2*P.N`，移动剩余为 `P.N`。原 `mediumAtlas` 使用同一 `beforeHBCutoff K js` 和 `originalMediumLow/High`。`js` 是单标签原 chart，不是借用两个 RealB mother。

`P1OriginalSingletonOneLongRectangle.actual_row_reindex` 已有通用 `K,Q,rho` 的逐行字典，使用同一个 `integerProfile`；本候选只读取该 profile 的支撑。它尚未提供 mediumAtlas 的完整分支重排和 restoring budget，也未把旧 one-long 终端重复包装为 medium 终端。原 `Params`、`W=N^omega`、small beta、fine word、global rough collision mask、实际 owner/history、`products/free` 均未改写；本局部几何对它们不作数值代换。

原 P1 schedule 的共同 `beta,k,K,kap,kap0,zeta` 仍必须在 N 前选定，再将本 eventual threshold 与其他有限阈值取大。该引理不会供应原 `forall N` history，也不会改变 pre-N 固定的历史深度 n。它不涉及 `savingMiddle`、raw→boxed transfer 或 ALL16 lower 系数。

## 已有工作与本次增量

旧 one-long 包已给出 `active_chart_geometry` 和单长支路付款，原 `original_cutoff_singleton` 也已存在；这些直接复用。已有 `P4BOriginalMediumFibreSWWindow.eventually_window` 是两个 RealB 原素数组的活 profile，不能直接用于 singleton。本件补的是一组实际 profile 到完整补积 fibre 的局部 window。

旧 `P5OriginalChartRoughCutoff`、`RestrictedResidueScale` 及 `Part3ActualRoughIntervalAllModuliSW.exists_original_chart_rough_AP_all_moduli` 也都存在。本件不重写 rough-SW 分析。新的 `x≤v≤x²`、`x^(2*zeta)≤U`、`2U≤x` 正好供应该 SW 接口的几何条件；真实截断为 `roughZ v`。选中角色的实 Möbius 截断、归一化 log、retained Fourier band、精确系数重构及总费用仍须按实际 singleton 源接线；本件没有把任意 rough 序列宣称为 SW。

只在已知相关 singleton/medium 源、旧 dependency registry、当前 publication index 和原手稿中做定向复用检查，没有重新扫 native6/全图。未发现已签同一个 singleton first-medium window 端点；这句话限定于所检查范围，不能解释为全仓库不存在未知源。

## 剩余真实分析输入

原 PP 文本 L 41–64 明列：每个 whole atom box 的四条 M licence，以及 uniform signed medium theorem。它们不由 import、表形状或本 window 自动成立。现有低首三粗槽 `P4BOriginalMediumLowThreeAdmissible` 只覆盖其明确的两组 family/rank-three 子族；更高低首词的当前分组问题仍保原 HOLD，不能拿此子族代替全部 final free 系数。

新 half-J 源 `Part3OriginalNativeJFromPrimeWeil.original_range` 已去掉 hJ/hHalf/hWeil 参数，且已有 source-math AL `c2611ba9…`。本件承认这项已有结果，不重做或重新标作缺证明。它量化固定 epsilon 与 A 后的统一 C，只给 `X≤A max(M,Q²/M)` 内的真实 pascadiJ 界。它不是整个 signed M、不等于全谱 7/32，也不自动证明原物理 packet 满足所有区间/尺度条件。原 Medium 文本 L 349–416 的普通/异常谱返回、计数归一化与误差恢复仍必须接回相同的系数、共同区间和相位。本轮没有新的完整 signed M 独审端点可据以撤销该 HOLD。

因此分类为：本次叶是**原稿内省略推导的 source candidate**；剩余 signed M 是**原稿明确分开的实质分析输入/尚未验收的实现**，不是本件发现原稿命题为假。更高词当前分组的路线问题也不能转写为原 whole-box 命题的反例。上一份 route-only AL 已撤掉的非必要 raw→boxed 强接口不再恢复。

## 验证边界

只做了源码逐行人工数学/接口审查、精确字节读取、hash 与已有 metadata 对照，以及 candidate 的 import/声明/禁用占位符静态检索。没有运行 Lean、Lake、LSP、项目 helper、candidate、fixture、guard、CI 或 quota；本轮没有 Git 读写、网络读取或下载。完整递归 import closure、兼容选择、elaboration 与 kernel 均待 ROOT 控制的后续验收。这里的“未编译”仅限定本件候选，不能覆盖掉历史 R22 全 102 kernel pass。

`SOURCE_PINS.json` 绑定三条直接 import 和逐项使用的关键源、原稿、旧审核。未把本地 computed blob 冒充新远端 tree 身份。旧 `fcb1d83…` 与 `e406a828…` freeze 保持逐字节不变；main 由 T10 独占，本件没有修改。

