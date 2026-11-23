# R02 · 三个原标记积分的具体价格

原稿固定为 `a988cba584d803ae2856a0de50efb582f4f3dd6a`。对应数值附录 530–555 行及 713–715 行。原 Y13 三个积分收费、Y12 三个原 $KJ$ 费用及其同一 $\rho$ 边界沿用。此表中的积分按 $K_0=67619/10000$ 归一。取 $M=10^{18}$，U7 和 U9 各用 32 个原 Taylor 阶，U8 用原二维网格。原 `Mesh` 的三个 predecessor 全为 999999999999999999。

| 原项 | 新的实积分上价，分母均为 $10^{16}$ | 原网格上包相对实积分的误差上限 | 离 $\mathrm{saved}U_j/K_0$ 的剩余严格差额 |
|---|---:|---:|---:|
| U7 | 2045919472026424 | $9.7440\,10^{-15}$ | $9.3336\,10^{-12}$ 以上 |
| U8 | 5999905266705567 | $3.4854\,10^{-14}$ | $7.8645\,10^{-10}$ 以上 |
| U9 | 4816743300211123 | $7.5606\,10^{-19}$ | $6.1727\,10^{-12}$ 以上 |

`R02_FINITE_EVIDENCE.json` 给出各栏的完整有理分数、五行证书、每个多项式的导数余量及两个 U7 多项式上界的精确积分。表中的误差数向上缩写，严格差额向下缩写。前述三个比较的形式就是原 `Mesh.rate_eq_zero` 的三项输入。`P6OriginalZeroMarkedIntegralCost.original_mesh_upper_prices` 的源声明直接给这三个不等式，`original_mesh_rate_zero` 直接给本数值见证的 `rate = 0`，`three_actual_integral_cost_nonpos` 作用于原 $(2,1,1)$ 带符号和以及任意非负 $H$。各项源码和验证状态分别如下。

## 原始证据与复用

已存档 `sharp-switch-midpoint-1024.json` SHA-256 `05286de6a5e8dc9671c0d7fc131c7e9aea190f2b53fc5d7abc1884fe11916e08` 含现稿采用的三个上端。`sharp-switch-simpson-independent.json` SHA-256 `55916ccef112e0a3eff02407a51fdec47f613e059f4809ee29b994590c13a6a7` 记录 64 分块、112 位向外舍入的独立双界。它的三个上端严格低于相应 midpoint 上端，除以 $K_0$ 的余量分别约为 $9.099\,10^{-12},1.339\,10^{-10},5.957\,10^{-12}$。本轮读取 9 项冻结绑定并核对哈希，未执行 64/1024 分块生产程序或任何原 17,572 行、430 步工作。

档案的两份 JSON 只存总上下端，未存逐块 Lean 见证。旧三种原 upper cover 分别已有 `rational_gap_le_totalRate`、`uniformUpper_error`、`actual_integral_errors_le_rate`。本轮新证书给这些显式误差率所需的实积分上价。程序 `verify_mesh_evidence.py` 从 Lean 原始整数 witness 复原有理式，逐项检查五组导数与锚点、原仿射变元、U7 两真对数因子的非负性、三个网格费用及 9 项旧绑定。执行结果见 `R02_FINITE_EVIDENCE.json`。此独立有限检查没有把 JSON 字段当作实积分不等式。

## 上价如何绑定到原实积分

在反向归一坐标 $x=(r-t)/(r-l)$ 上，每个 witness 给出有理系数多项式 $P$，三个正分母测试以及 $A=a+bx$、$B=c+dx$、$D(x)$。令 $V=DP-\log(A/B)$。用 24 项指数下和验证 $\exp(D(0)P(0))\ge A(0)/B(0)$。对导数分子
\[
 AB(DP)' + ad-bc
\]
逐项检查常数项加所有负尾系数的有理下界大于零。因 $0\le x\le1$，整个实区间有 $V'\ge0$，从而 $\log(A/B)/D\le P$。反向坐标下多项式积分精确等于 $(r-l)\sum_k P_k/(k+1)$。五个 witness 度数依次为 U9 45、U8 154、U7 素支 69、U7 订正第一因子 27、第二因子 22。对于乘积，原两个真因子在整个区间非负，分别检查两端 $A\ge B$，再用两份上界相乘。

U9 复用 `currentChenUpsilon9HarmonicIntegral_eq_logIntegral` 以及原右开区间/区间积分字典。U8 从 `P2NegativeDomainCover.eighthHarmonicIntegral_eq_nested` 出发，在下端 $u=1/3$ 代入旧通用实内积分 `currentChenUpsilon9Harmonic_inner_integral`，给出 $\log(2-3t)/(t(1-t))$。两者分别对接 `P6OriginalNinthMeshPrice.ninth_mesh_passes` 与 `P6OriginalEighthMeshPrice.eighth_mesh_passes`。

U7 从同一个 Buchstab 原双积分出发。`p5U7Omega_kernel_first`、`p5U7Omega_kernel_second` 和 `kernel_branch` 将全三角分成原有首项与 $u<(1-t)/3$ 的订正。首项内层复用与 U8 相同的 `currentChenUpsilon9Harmonic_inner_integral`。源码待验的 `full_original_seventh_dictionary` 将这个逐点分解升级为原 Omega 全积分的等式。已验独立解析模块计算的是完整原三角区域上订正分支的双积分。取 $v=(1-t)/u-1, f(v)=\log(\max(1,v-1))/\max(1,v), F(v)=\int_2^v f$。对 $u$ 求导可得每个半素行等于 $F(1/t-2)/(t(1-t))$。再取 $d=59/250$、$w(v)=\log((1-d)/(d(\max(1,v)+1)))$、$G(v)=\int_2^v fw$、$L(t)=\log((1-d)t/(d(1-t)))$。在原 $t$ 区间有 $w(1/t-2)=L(t)$，所以 $L(t)F(1/t-2)-G(1/t-2)$ 的导数恰等于该行。代两端得到稿件数值附录 542–547 行的订正积分，原上限为 $132/59$。`literal_double_correction_identity` 的陈述展开了双区间、开闭 seam 及原两个对数；`P6OriginalSeventhMeshPrice.seventh_mesh_passes` 连接原三角覆盖。

## 原范围和工程验收

`R02_SOURCE_SELECTION.json` 和 `R02_NATIVE_SOURCE_IDENTITIES.json` 对每个入口列出原 project 模块列表、SHA-256、直接导入、来源以及快照时本地缺失的原生 API。旧数值调用选用 Y13 `P6OriginalMarkedIntegralPrices` SHA-256 `7c38e1b2b9ff64030d25841e2e4e4e94717c61aea98cd5588b067ca672f99a97`。其 Y13 调用端仍是 `P6OriginalSameRhoEndpointRows` SHA-256 `5250cdd54ccc308c415d2b89adf0a70ebb45f00558b68beee4fc7c3d36785c9a`，Y12 输入口仍是最终选版 `P5OriginalFineSwitchedCosts` SHA-256 `49742a8ed0e0ec51efe8e49731960e23470200d0ae3323363fc3970294079988`。新模块各自公理/内核/编译收据按实际执行单列；以下统计包含入口本身。

| 验收层 | 导入图中的 project 模块 | 当前证据 |
|---|---:|---|
| 多项式 soundness | 1 | `P6OriginalLogPolynomialBound` 准确 source SHA da3209091590ab185b4e83b1f4f28d77122fcad281d6104b25d976fe99ac44d9，经编译、独立内核及全部 11 声明类型/公理审查通过 |
| 五组有限证书及四个真实一维积分 | 3 | P6OriginalLogPolynomialRows 的全部 5 条证书已于 1b33f021c87b6be8df47457bd46f314654365d144b5a8d9b27480406ff74b328 编译、独立内核及类型/传递公理通过。P6OriginalLiteralLogIntegralPrices 在 5011dc730e990f4c9140e43508d2decd1c2c24ac8e52bef2606771639294eb45 下编译、独立内核与 4 条实积分不等式的类型/传递公理均通过 |
| 真实积分加完整有理误差率的严格价格 | 4 | `P6OriginalLiteralMeshPrices` SHA-256 `7ba66231140d023e4de4210010c8556ba79fe38598aedeef7add4e3cac3a3272`，编译 4.94 秒，独立内核重放、5 个完整类型及传递公理通过；`literal_three_mesh_budgets` 同时给三项严格差额 |
| 独立 U7 原订正项双积分恒等式 | 1 | `P6OriginalSeventhCorrectionIdentity` SHA-256 `4fbf1507eba75818d7cd1f725714659b3b3f78c6693b209ab53789137627e3d6`，编译 12.73 秒，独立内核重放、6 个完整类型及传递公理通过；`literal_double_correction_identity` 保留订正分支的完整原三角区域；完整 Omega 积分字典仍待验 |
| 按原名字的 U8、U9、U7 有理上包 | 87、176、112 | 上述三个无前提源声明；旧依赖另缺 6、14、9 个直接导入的原生 API 对象，原模块编译、内核与传递公理未验 |
| 顶层原 `Mesh.rate=0` 和三项合计 | 208 | 全部 project 源能定位，另外 16 个直接导入的原生 API 对象未安装；按固定 goldbach-lean 源继续追踪为 810 个原生源模块和包外 Architect 入口。未完成同版完整验证 |

这五个源模块的 31 条公开定理均有同源编译、独立内核重放、完整类型和传递公理收据。五次审查合计仅报告 `propext`、`Quot.sound`、`Classical.choice`。原命名入口及三个 cover 桥另有 12 条源声明。

Y12 的 `P5OriginalFineSwitchedCosts.three_costs` 对每个 $j$ 分开收取 $KJ_j$。本数值见证逐项给 $J_j\le\mathrm{upper}_j\le\mathrm{saved}U_j/K_0$。由于 $K\ge 0$，用已有 `original_upper_price_gaps` 可分别得到 $KJ_j<U_j\mathrm{Envelope}(k_*)$，每个局部 $\delta_j$ 仍留给本项的原误差。

在原 `P6OriginalSameRhoEndpointRows.weightCost` 中代入 `originalMesh` 后，按定义与 `original_mesh_rate_zero` 化简，所得权重为 `remainingGroupCost N E + 2*seventhError s N + eighthError s N + ninthError s N`。同一选择 `s` 的六个原 marked PP 测试、原例外集合 `E`、共同阈值及三个端点的原系数均保留。

Y12、Y13 保留各自整叶合同。八组同一实际实例还需要始行、U3/U4、U5、U6、U10/U11 五组带符号估计以及 U7–U9 的六项同源物理 PP 测试。Y13 另需原 outer signed PP、全部实 $b$ 的统一算术上界、原下界及三个端点的共同阈值。原 1,664 项门、13 实际叶和 23 汇总父项均保持原范围。

公开文件按验证状态分为两个目录。逐模块位置与准确 SHA 见验证目录的 `SOURCE_FILES.json`。这里没有把源码依赖已定位等同于完整编译通过。
