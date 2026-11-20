# P4 E1 四源独立增量审查

**裁定：AL，限于实际光滑 long family 的 N2-priced E1、同一 Q/rho 的归一化单因子 mean-error 接口，以及真实 chart Z 上的 B2 gap。** N2 代替 N1 在这里确实只增加固定对数价格，没有额外 q、D、除子或 x 幂；下文给出明确价格与原两长路线的适用性核算。没有发现本包新增的实质数学阻断。

**本包未编译，elaboration/kernel 验收保持 HOLD。** 未审签一般 C1/N1-optimal E1；没有把 pair/E3、twice-mean、sharp endpoints、母积分、log54、H_N 或 hUpper 记为完成。旧 E4 七源及其审查不重证、不重签。

## 1. 固定对象与检查

审查者 `/root/n21_p4_branch_review`，非作者。日期 2026-11-21。

freeze 为 `rough-coprime-mean/FREEZE.json`，26909 字节，SHA256 `555650242b0fc586d9327e39471406fea926b04f2bc9b7ab3f3f2d647967bbd7`。SOURCE_RECEIPT 为 `80529172ed1accfe687309cead54a6c6765a0f34fbff52d260392746c1f924e4`。

45 pins、7 个包文件逐项 bytes/hash 匹配；39 个词法声明的行号/前缀匹配。新终端 `eventually_live_same_rho_E1` 的完整源码类型（ActualChart 63–86，保留所有内层 let）词法 SHA256 为 `888f2f67d9f28d1445674ab5966d28b78c92bf0dd53e0c7914b1a7f18a68417b`。详见 `VERIFICATION.json`；没有把词法读取称为 Lean AST 或已 elaborated 类型。

| 简称 | 新文件 SHA256 |
|---|---|
| Smooth = P4BOriginalCoprimeSmoothE1 | fc91fd4774c15426250da912bf8644dd064bb5cf81b70dbf968b96142ead964a |
| Brun = P4BOriginalBrunCoprimeE1 | 33a7cfed296bf49fdf00eaa554525d9f84ccabac90bd55480277a7fb34019ea3 |
| SameRho = P4BOriginalSameRhoCoprimeE1 | d56b7b69348be86123687e75307f775def172addec0445d723f07801df12489e |
| ActualChart = P4BOriginalActualChartCoprimeE1 | 18f78d6a4d5ad91fee5f15d998653c4647ac181f16c0469bfd774e7ff2f67cc3 |

只运行 source/JSON/hash/词法检查；未运行 Lean/Lake/LSP/kernel/helpers/validators/fixtures，未加载对象、下载、操作 Git/GitHub/CI/额度或派发。未改作者或旧包。

## 2. 实际 progression primitive 已供应

Smooth 39–73 的 `poisson_E1` 消费的是旧真实 `affine_periodization_poisson`，不是旧 Phase7 的 `hprogression` 包装器。旧 Phase7 `literalE1_from_progression` 93–105 明确仍把每个 eligible divisor 的 progression error 作为前提；新包没有调用它。

新证明中的真实 zero mode 为 `(U/D) * Fourier(F)(0)`，32–34 证明 `Fourier(F)(0)=∫F`。原 affine-lattice 相位不改；非零正、负整数频率全部保留，以

`t=U/D>0,  sum_(h≠0) t/(1+|t*h|)^2 ≤ 2`

乘旧实际 Fourier 衰减 `C_F*N2(F)/(1+|ξ|)^2`。旧 `Part3SmoothProgressionError` 60–82 的两侧 telescoping 证明对每个 t>0 成立，故误差是 **2 C_F N2(F)**，不含 U/D、q、D 或其逆的额外价格。D>U、U/d<1 也没有被排除。

Smooth 75–88 通过旧 `natural_progression_eq_periodization` 的正支撑 bijection 回到同一 `wideWindow U`，没有遗漏自然数/整数或端点。Smooth 93–145 对原 Möbius indicator 作有限交换，调用旧 `reciprocal_moebius_totient`，得到精确 `U*phi(q)/q*∫F`。这不是 unrestricted Euler mean 近似。

Smooth 151–183 的插入除子换元保持 F 本身不变，只将尺度改为 U/d。若 `(m*d,q)>1`，真实互素均值与该主项同时精确为零；否则应用上述对所有正尺度统一的界。旧 `profile_N2_cube` 的 U 参数仍是原 U，因此 log(d*u) 与 Mellin phase 的原比例被保留，没有误改为 log u 或凭空付出 d 的导数幂。

## 3. Brun E1、非单位与均值归一化

Brun 25–34 定义的 mean 是原 n-sum，含实际 upper/gap polynomial 和 `(m*n,q)=1`；density 是同一 `brunSupport Z (2j+1)` 中保留 `(m*d,q)=1` 的 reciprocal coefficient 和。

Brun 45–99 通过精确 divisor expansion、原 coefficient 的一有界性和 support card≤Z^(2j+1)，得

`||mean-main|| ≤ 2 C_F N2(F) * tau(q) * y`,  y=`Z^(2j+1)`。

这里是每个 q>0、每个 m 的实际估计。q=1 有显式 `modulus_one_mean`；q=2 无奇偶例外。m 可以为0或含重复 HB 素因子：非单位 gate 正确保留；q=1 时 m=0 的 coprimality 判定也未被擅删。

SameRho 23–78 的 pairMean 保留**恰好一个** 1/phi(q)。先按 `(short,q)` 分支，然后才将两长互素均值因式分解。pairMain 的系数因此为

`(1/phi(q)) * (U*phi(q)/q) * (V*phi(q)/q) = U*V*phi(q)/q²`。

`pairMean_E1_remainder` 保留 `rF*mainG + mainF*rG + rF*rG`，没有删掉任一交叉项。它只是恒等展开，未宣称 E3 已支付。

Generic E1 不涉及 AP 目标 N，因而没有伪造 target-coprime 前提；SameRho 87–90 从真实 Q 的 `support_coprime_target` 证明非 primitive target 模数不属于 Q。全部除子换元仍在原 q 上，不是 qd 或 qd1d2。原 signed rho 在完整 mean−main 成形后才取范数；没有把原 signed beta/short mean 改成绝对均值。

## 4. N2 价格对实际任务可承担：明确指数

新包并未证明所有一般 C1 函数的 N1 最优式。它证明原实际 C-infinity compact family 的 N2 式，并由 Brun 135–153 内部调用旧 `profile_N2_cube`，不把 N2 上界外包为假设。

令 L=log x≥1，s=`bandwidthOrder(A0)+1`，delta=L^(−B)，freq=L^s。真实 live 原坐标有 1≤U≤4x：这是原 tuple 的正乘积与 `tuple_scale` 的直接结论，对这里的任意选中坐标都适用。旧 `logSize_le_scaled` 给

`logSize U ≤ (4+log 4)*L`。

故实际 profilePrice 满足明确统一界

`profilePrice(delta,U,freq) ≤ 8 C_F C_profile (4+log 4) L^(2B+2s+1)`。

SameRho 94–129 从同一 actual Q 的 positive/squarefree/|rho|≤1 与 active v≤D 推出固定 reciprocal moment；只用 tau≤tau^4，不引入 D 的正幂。D=floor(x^(1199/2000))≤x，故其 log16 因子≤8^16 L^16。于是新终端的全部右端实际上为

`≤ C * x^(1/16000) * L^(2B+2s+17)`，

其中 C=`8 C_F C_profile (4+log 4) 8^16` 与 row、q、short、Z、xi 无关。任意所需固定额外 log 精度或以后 log54 均可通过正 power gap 吸收。此处是已陈述 priced E1 的适用性核算；终端类型本身仍输出上述带 profilePrice 的界，没有冒称已经写出完整 rough E4 的任意 A 定理。

对原两长 E1 用法，N2 额外价格不会破坏其余 power remainders。具体地，source66 已选真实两长，原 lower-product 恒等式及 live tuple 给 `M*U*V≤4x`；long 门 `U,V>X^(1/3+ζ/4)`、x≤4X 在进一步固定 scalar 阈值后给 min(U,V)≥x^(1/3)。这只是把常数4吸收进 ζ/4，并不另造更小的 family。因而在 y≤x^(1/16000)、M≤x^(40ζ)、ζ≤1/400 下：

* `M*(U+V)*y ≤ 8*x^(2/3+1/16000)`；
* `M*y² ≤ x^(1/10+1/8000)`；
* leading gap 仍为 `MUV*exp(-(loglog x)^2)` 乘固定 log 幂。

所以用 N2 给 E1 的一次/二次误差价格仍全部可付，且不需要额外模数幂或增长 divisor-moment order。**这些数值核算不是本包已完成 E3 的宣称。** 后续 pair/E3 组装必须用逐 q 的 `actual_E1` 加绝对 reciprocal moments；不能把已求和的 `signedError` 范数直接乘一个依赖 q 的 `mainG(q)`，那样会误用 signed cancellation。新包已有正确逐 q 供应，所以这项边界不阻断本 E1 AL。

## 5. 同一真实 Z 的 B2 与 y 同时成立

Brun 114–130 把当前 complex density 精确识别为旧 nonnegative `compatibleGapDensity`，在同一 `smallPrimes Z`、同一 order、同一 q-deletion 和 m-gate 上调用 `actual_B2`。没有删除碰撞或重建另一个 alphabet。

ActualChart 36–57 的新 gap 证明没有套用仅适用于 roughZ(x) 的旧 epsilon(x)。它使用旧 `eventually_real_chart_harmonic` 的正确更强量词：阈值在 x 上先取，随后对**任意**全部 prime≤x 的有限 alphabet P 统一有 harmonic(P)≤2 loglog x。实际 Z≤x，因此 P=smallPrimes Z 可直接代入。

记 L2=loglog x，r=2 floor(L2²)+1。旧 `nextOrder_bounds` 给 r≥L2²；旧 factorial estimate 给 `H^r/r!≤exp(e²H−2r)`。在 H≤2L2、L2≥2e² 时，其指数≤−L2²。得到原密度对所有 q、short 同时满足 `||gapDensity||≤exp(−L2²)`。

同一个 actual Z 仍为 `beforeHBCutoff K [cj,ck]`，source66 已付 `1≤Z` 与 y=Z^r≤x^(1/16000)。ActualChart 111–117 从 r≥1 推 Z≤y≤x，故 B2 的 alphabet gate 不需另选 cutoff。支撑 epsilon=1/16000 与 factorial gap epsilon 是两个不同量，源码使用关系正确。gap superlog 项没有被乘上 y；y 只出现于 E1 的 power errors。

## 6. 统一阈值与剩余接口

ActualChart 87–93 先固定 K、B、A0、ζ、κ、kap0，合并真实 chart Brun、smoothing schedule 与 gap 的 `∀ᶠ x`，取 x0，再通过原 `eventually_live_large` 得共同 N filter，同时合并 local level 与 original retained-cube twists。94 行之后才引入动态母维数、cj/ck、blocks、source tuple 和选中位置；119 行之后才引入 policy/rho/S、retained xi、profile/Brun labels 和 short。

因此阈值对随 N 增长的 rows、所有当前 q、所有 retained xi 和原 chart labels 统一。hRange 是已固定同一 final FineDensity 族的 `.599` 物理支撑；没有 hMeanGap/hprogression/hModes/PP 等目标形新前提。E1 对任意 coordinate 的成立比实际两长调用更宽，不是放弃原两长所需条件而换成无用定理。

原补篇 298–306 明确要求 E1 的真实 phi(q)/q 均值；308–338 另列 product sandwich、twice-mean 及 E4 合流。本包对这些职责的划分准确。下一步仍要实际组装 E3 的非负 majorants/两份 mean，控制 individual endpoint strips，并接回原 signed HB mother amplitude 和 H_N。pairMean 的代数身份、单因子 signedError 与本次 AL 均不能取代这些步骤。

精确传递源码选择、elaboration 与 kernel replay 未执行；不会因本审查新增形式通过或完成整个 P4。
