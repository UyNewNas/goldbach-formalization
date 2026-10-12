# Part 3 第二轮：真实 rough 槽辅助 SW 的推进与剩余输入

## 交付结论

本轮在 `chatgpt/chen-p3-distribution` 的真实最新检查点
`64598da177adf861df3763d7c465ff941388b6d6` 上继续。共同基线仍为
`1a80c1bcce67886f699d097fc37fd245cd3620bf`，未收到替代该基线的 Part 0 完整 SHA。
手稿、工具链、全部依赖与常数保持 [README](README.md) 中的固定值。

选中的核心步骤是冻结 prime-product 补全第 5 节的**实际 rough 槽统一辅助 SW**。
本轮完成两项独立估计及其归一化的数学推导，并写出完整 Lean 证明候选：

1. 对同一复系数与同一区间，加入 `(n,k)=1` 的代价为
   `2*omega(k)*H/z ≤ 2*tau(k)*H/z`。
2. 对任意一有界复系数，真实 AP 误差至多
   `H/q+2+H*c_R*log(H)/min(q,H)`，包括 `q>H`。

二者结合后，原有 `MediumAdmissible` 上的 `UniformAuxiliarySW F 1`
只需另供**同一实际族、`k=1`、`q<log(x)^(A+2)` 的统一小模数 SW**。
这项小模数输入仍未证明；本轮没有把它藏进结构字段，也没有把 full SW 或
dispersion 结论当作新参数。

**所有本 Part Lean 定理仍为候选，编译器确认的类型清单为空。** 原版 Lean 的
唯一一次新启动探测仍失败在源码解析前；无同源成功编译记录可复用。源类型全集见
[THEOREM_TYPES.md](THEOREM_TYPES.md)，实际执行证据、源码哈希与独立源码审查见
[VERIFICATION.json](VERIFICATION.json)。

## 1. 旧五模块的修复与检查

| 模块 | 本轮实际工作 | 编译／内核／公理状态 |
|---|---|---|
| `Part3DistributionTargets` | 对照 frozen 类型，保持定义、物理模数、共同相位和量词原样 | 均未完成 |
| `Part3PrimeAPDistribution` | 把共同区间定理中的 `abs_sub_le _ _` 修为 `abs_sub _ _`；逐项核对真实 BV API | 均未完成 |
| `Part3CurrentLowerDistribution` | 全文件对照实际 Y3–Y6 selector、`BoundingSieve.rem`、完整模数和中心成本供应者；未定位第二个确定错误 | 均未完成 |
| `Part3LongSlotDistribution` | 全文件对照区间计数、逆元互素方向、精确 coprime mean 与复系数范数 API；未定位确定错误 | 均未完成 |
| `Part3LongSlotNormalization` | 核对两个实际 power/log 供应者和统一阈值顺序；保留未加 rough 筛选的整数槽范围 | 均未完成 |

修复位置是 `part3_abs_sum_mul_primeAPIntervalError_log_saving` 的最后一步。
固定 mathlib 的 `abs_sub_le a b c` 是三点三角不等式；这里需要的是
`abs_sub a b : |a-b|≤|a|+|b|`。修复没有改变目标类型或常数 `2`。

当前 lower 的主定理仍按 `∃B≥0, ∀epsilon>0, ∀ᶠN, ∀Q, ∀hN, ∀S3 S4 S5 S6`
排序；`B` 先于 `epsilon`，同一阈值覆盖所有实际行。它包含全部中心修正，物理
模数前提仍是 `p*e` 或 `p1*p2*e` 落在 BV cap 内。这里没有把普通 BV 的平方根
cap 升格为 `theta_*=599/1000` 的供应者。

长整数槽的 `2*||alpha||_1*||rho||_1` 界保持原定义：长槽是未加额外筛选的整数
区间。它没有被接成 rough 长槽、素数长槽、任意长槽加性相位或两长槽的分布供应者。

## 2. 所选核心的真实算术对象

[Part3RoughAuxiliarySW.lean](../../ImbalancedChen/Part3RoughAuxiliarySW.lean)
定义同一个实际误差：

\[
E_{S,\alpha}(k,q,b)=
\sum_{n\in S}1_{n\equiv b\ (q)}1_{(n,k)=1}\alpha_n
-\frac1{\varphi(q)}\sum_{n\in S}1_{(n,kq)=1}\alpha_n.
\]

这里 `S⊆Ioc 0 H`，`H` 是正整数载体的**绝对上端点**，不是任意平移区间的长度。
两端使用同一 `S`、同一 `alpha` 和同一精确 coprime mean。`b` 可变；删除误差和
大模数界甚至不要求 `b` 原始。最终 SW 接口仍保留手稿的 `(b,q)=1` 条件。

实际系数实例是：

\[
\begin{aligned}
\texttt{roughOneSlot}(z,n)&=1_{\forall p\mid n,\ p\text{ prime}\Rightarrow p>z},\\
\texttt{roughMoebiusSlot}(z,n)&=\mu(n)\,\texttt{roughOneSlot}(z,n).
\end{aligned}
\]

`mu` 使用实际 `ArithmeticFunction.moebius`。符号一直保留在原误差和中。
`auxiliarySWError_sub_one_norm_le_mellin` 另允许任意实数 `t` 的单位扭转
`alpha(n)*(n:Complex)^(I*t)`，通过正整数上 `||n^(it)||=1` 证明其合法性。
一般复系数版本也容纳共同单位加性相位；这些允许性只作用于下面已经推导的删除
误差和大模数分支，**不推出任意相位下的小模数 SW**。

### 2.1 辅助 `k` 的代价

设 `A` 是被辅助互素条件删去的 AP 质量，`B` 是被删去的 `q` 互素质量。
实际有限和逐项相减给出

\[
E(k,q,b)-E(1,q,b)=-A+B/\varphi(q).
\]

`q>0` 给出 `phi(q)≥1`，因此

\[
\|E(k,q,b)-E(1,q,b)\|
\le2\sum_{\substack{n\in S\\(n,k)>1}}\|\alpha_n\|.
\]

若 `||alpha_n||≤1`，且非零系数的每个素因子都大于 `z>0`，每个被删去的非零
项都是某个 `p|k,p>z` 的倍数。对 `k>0`，有限素因子覆盖和实际正倍数计数给出

\[
\sum_{\substack{n\in S\\(n,k)>1}}\|\alpha_n\|
\le\sum_{\substack{p\mid k\\p>z}}\lfloor H/p\rfloor
\le\omega(k)H/z\le\tau(k)H/z.
\]

这里使用 `Nat.Ioc_filter_dvd_card_eq_div`，没有平移区间的 `+1` 损失，也没有对
`k` 的大小加上隐藏限制。最终有限定理的完整类型为：

```lean
theorem auxiliarySWError_sub_one_norm_le
    (S : Finset ℕ) (α : ℕ → ℂ) (H k q b : ℕ) (z : ℝ)
    (hS : S ⊆ Finset.Ioc 0 H) (hz : 0 < z) (hk : 0 < k) (hq : 0 < q)
    (hα : ∀ n ∈ S, ‖α n‖ ≤ 1)
    (hrough : ∀ n ∈ S, α n ≠ 0 → ∀ p : ℕ,
      p.Prime → p ∣ n → z < (p : ℝ)) :
    ‖auxiliarySWError S α k q b - auxiliarySWError S α 1 q b‖ ≤
      2 * (k.divisors.card : ℝ) * (H : ℝ) / z
```

这是源码提取类型，尚非编译器确认类型。它的前提中没有 SW、dispersion 或所求误差
结论。对实际 `MediumAtom.alphaCarrier` 取 `H=floor(2U)`，便得到 `4U*tau(k)/z`。

### 2.2 大 `q` 分支：保留 `q>H`

真实同余类计数和一有界性给出 AP 项范数 `≤H/q+2`、coprime 主质量范数 `≤H`。
复用 pin 内的标量供应者
[primeSW_reciprocal_totient](https://github.com/subfish-zhou/goldbach-lean/blob/09b97db5764ade1246bfb77206baa1b124760958/MathlibNt/AnalyticNumberTheory/LargeSieve/LiLiuFouvryPrimeSWLarge.lean)：

```lean
{N d : ℕ} → 3 ≤ N → 0 < d →
  (1 : ℝ) / d.totient ≤
    richertReciprocalTotientConstant * Real.log N / (min d N : ℕ)
```

这个供应者没有素数源前提；`d>N` 分支使用 `log(d)/d` 单调性。因此它可合法用于
上述任意复系数的精确主项。设其固定正常数为 `c_R`，得到

\[
\|E(k,q,b)\|\le H/q+2+Hc_R\log H/\min(q,H). \tag{R2-large}
\]

该有限定理允许所有自然 `k,b`、所有正 `q`，无需 roughness 或 SW。Mertens 型
标量界在这里只支付大模数主项；它没有被当作小模数分布或 signed medium 抵消。

## 3. 统一阈值与直接接入原 medium 范围

[Part3RoughAuxiliarySWNormalization.lean](../../ImbalancedChen/Part3RoughAuxiliarySWNormalization.lean)
写出两条独立的归一化链。

第一条保留手稿原阈值
`z(x)=x^(1/(log(log x))^3)`。从

\[
\frac{(\log\log x)^4}{\log x}\longrightarrow0
\]

得到任意固定 `B` 的 `log(x)^B≤z(x)`，再得到任意 `epsilon>0`、固定 `A` 的
`4/z(x)≤epsilon/log(x)^A`。因此一个 `x0(A,epsilon)` 同时控制所有 atom、
区间、复系数、`k,q,b` 的辅助删除误差：

\[
\|E_d(k,q,b)-E_d(1,q,b)\|
\le\epsilon\,U\tau(k)(\log x)^{-A}.
\]

第二条固定 `xi>0`，令 `x^xi≤H≤2x` 且 `q≥log(x)^(A+2)`。同一大尺度阈值保证

\[
\log(x)^{A+2}\le H,\quad
\log H\le2\log x,\quad
\min(q,H)\ge\log(x)^{A+2}.
\]

于是 `(R2-large)` 除去端点常数后至多
`(1+2*c_R)*H/log(x)^(A+1)`。它用 `epsilon/2` 支付；真实端点成本 `2` 由
`(4/epsilon)*log(x)^A≤x^xi≤H` 支付另外一半。得到的完整源码类型是：

```lean
theorem eventually_auxiliarySW_large_modulus_logAccuracy
    (A epsilon xi : ℝ) (hepsilon : 0 < epsilon) (hxi : 0 < xi) :
    ∀ᶠ x : ℝ in atTop, ∀ H k q b : ℕ, ∀ S : Finset ℕ, ∀ α : ℕ → ℂ,
      S ⊆ Finset.Ioc 0 H → x ^ xi ≤ (H : ℝ) → (H : ℝ) ≤ 2 * x →
      (Real.log x) ^ (A + 2) ≤ (q : ℝ) →
      (∀ n ∈ S, ‖α n‖ ≤ 1) →
      ‖auxiliarySWError S α k q b‖ ≤
        epsilon * (H : ℝ) / (Real.log x) ^ A
```

这里真实 `q` 没有上界，所有参数位于同一个 `atTop` 阈值之后。`xi` 是事先固定的
正数，不能随 atom 缩到零。对 medium 取 `H=floor(2U)`、归一化精度
`epsilon/2`，由 `U≤H≤2U` 得到 `epsilon*U/log(x)^A`。

**这个正幂下界不要求新增 policy 数据。** 原有 admissibility 中
`1≤Q1<U*x^(-sigma)` 直接推出 `x^sigma<U`，由
`MediumAdmissible.alphaScaleLower` 写出完整证明。故可用原 `sigma>0` 作 `xi`。

最终接入类型如下；唯一的分析前提 `hSW` 完全展开：

```lean
theorem uniformAuxiliarySW_of_mediumAdmissible_small_moduli
    {ι : Type*} (F : ι → MediumAtom) (B : ℕ) (sigma kappa c0 : ℝ)
    (hsigma : 0 < sigma)
    (hadmissible : ∀ i, MediumAdmissible B sigma kappa c0 (F i))
    (hSW : ∀ A : ℝ, 0 < A → ∃ C : ℝ, 0 < C ∧ ∃ x0 : ℝ, 1 < x0 ∧
      ∀ i : ι, x0 ≤ (F i).scale → ∀ q b : ℕ,
        1 ≤ q → (q : ℝ) < (Real.log (F i).scale) ^ (A + 2) →
        Nat.Coprime b q →
        ‖(F i).auxSWError 1 q b‖ ≤
          C * (F i).U / (Real.log (F i).scale) ^ A) :
    UniformAuxiliarySW F 1
```

大模数拼接先取 `max C 1`，辅助删除再取 `C+1`；各阈值只作有限的 `max`。
family `F` 固定在常数选择之前，family 成员 `i`、区间、频率、`k,q,b` 均位于
阈值之后。没有逐 atom 或逐 `k` 的阈值替代。

## 4. 尚未闭合的实际小模数 SW

冻结 [prime-product 补全](https://github.com/UyNewNas/chen-imbalanced-semiprimes/blob/ba6ec11d800eccc54406490631895e174de85766/paper/source/modules/distribution-prime-product-completion-20261010.txt)
第 5 节的真实槽是

\[
\alpha_n=\epsilon(n)1_I(n)1_{P^-(n)>Z_{\rm chart}}h(n)n^{it},
\qquad\epsilon\in\{1,\mu\},
\]

其中一有界正规化与固定 polylog 变化／频率预算必须一致。
该文件第 88、111–112 行的 `(S)` 使用
`Zchart=f(2^(6*k_star+2)*Xplus)` 并要求 `f(x)≤Zchart`。这条实际 chart 到 local
roughness 的尺度桥仍须在实例化时给出；本轮没有改写 `Zchart` 为较小阈值。

剩余命题恰为上一节 `hSW`，分别对这两个真实槽族、所有共同端点和许可频率成立。
pin 中可找到的 SW 供应者有：

- `primeSW_uniform_eventually`：真实 prime-indicator 源，保留辅助互素条件；不能直接替换成含合数的 rough `1` 或 rough Möbius 源。
- quadratic/nonquadratic primitive character 的 Siegel–Walfisz 供应者：对象是 von Mangoldt 的 `psi(N,chi)`；未定位实际 Möbius 的统一 SW 供应者。
- Möbius 的 Dirichlet 级数恒等式和绝对收敛域结果：不提供这里的小模数、共同区间、许可频率 SW 误差。

手稿第 5 节所列偶 Brun 阶 `2*floor((log log x)^2)`、下一层支持
`Zchart^(h+1)<U^(1/4)`、Möbius 互素分拆、最小内尺度 `U^(9/16)` 和总尾项
`O(U^(29/32)*log(U)^4)`，都仍需在真实系数类上完成统一误差证明。不能把尚未
供应的 classical Möbius SW 与这些重组自动当作已完成；剩余工作有实质分析内容。

## 5. medium (18)、(23)、(24) 的准确供应者差异

以下位置均指冻结 medium 补全 blob
`19f9672bc9b6d455045213c5e23e10433a9569d2`，而非旧 unrestricted 草稿。

### (18)：已存在完整 Weil，缺少实际频率聚合

第 261–279 行的 (17) 需要

\[
\left|\sum_{(n,\ell)=1}w(n/N)e(A\bar n/\ell)\right|
\ll\tau(\ell)^2\sqrt\ell+(N/\ell)\gcd(A,\ell),
\]

随后在 `A=a*(h*r'-h'*r), ell=q*r*r'` 上导出 (18)。pin 的
[LiLiuPrereqFouvryCompleteWeil](https://github.com/subfish-zhou/goldbach-lean/blob/09b97db5764ade1246bfb77206baa1b124760958/MathlibNt/AnalyticNumberTheory/LargeSieve/LiLiuPrereqFouvryCompleteWeil.lean)
确有无条件

```lean
theorem completeKloosterman_weil (q : ℕ) [NeZero q] (a d : ℤ) :
    ‖completeKloosterman q (a : ZMod q) d‖ ≤
      (q.divisors.card : ℝ) * Real.sqrt (q.gcd (a.natAbs.gcd d.natAbs)) *
        Real.sqrt q
```

同文件的 `reciprocalInterval_fouvry` 要求区间长度 `≤q`，且把
`sqrt(gcd(q,d))` 乘在整体界上。它不能直接充当把 Ramanujan 零频率单列的 (17)。
仍缺平滑完成／Poisson 频率桥、`h*r'-h'*r=0` 的单独计数、非零 determinant
和 gcd 二阶聚合及 E1 的原归一化组合。`tau(0)` 不能用于零 determinant。
第 282–285 行的 `q'=d*q` 权重重组只在 E1 得到许可，不能携入 E2。

### (23)：已有最后的谐调 gcd 界，缺少前面的真实碰撞范数

第 329–347 行实际系数来自
`z=s1*s2, y=f*(h1*s1-h2*s2)≠0`，需证明

\[
B_\nu^2\le x^\epsilon(1+H/S)(HS)^2F/\nu.
\]

pin 的 [LcmWeightBounds.sum_gcd_div_le_tau_log](https://github.com/subfish-zhou/goldbach-lean/blob/09b97db5764ade1246bfb77206baa1b124760958/MathlibNt/AnalyticNumberTheory/LargeSieve/LcmWeightBounds.lean)
已经支付 `sum_(g≤2S) gcd(g,nu)/g ≤ tau(nu)*(1+log(2S))`，本轮没有重复包装它。
仍缺上述 tuple 映射的 collision norm、相同／不同 h 对分拆、互素约化后的
`(m1,m2)=(j*v,j*u)`、保留 `nu` 整除产生的 `1/nu`，以及独立零差成本。
其它 Fouvry resonance-count 文件的标签和 determinant 尚未与此实际映射对应。
用任意平移倍数计数的 `+1` 替代非零倍数计数，会丢掉本步的 `1/nu` 精度。

### (24)：所需共同区间／packet 谱返回仍无匹配供应者

第 349–380 行的返回保留

\[
\begin{aligned}
|L_V|^2\ll x^\epsilon P_0\{&
\sum_\nu(|a|\nu)^\theta(U/\nu+Z+T_0)(V+Z+T_0)B_\nu^2\\
&+(C^2Z)^\theta(U+Z)^{1-\theta}(V+Z)^{1-2\theta}B_{\rm all}^2\},
\end{aligned}
\]

其中 `theta=7/32`、`P0=V*C^4*Z/(|a|*V*U+C^2*Z)`、`T0=|a|*V*U/C^2`。
所需条件包括 `(a,z)=1`、所有 level 共用实际非零 `m` 区间和加性相位、
`1_((n,a)=1)*beta(nu*n,z)*e(-n/z)` 的完整 transformed coefficient、所有 oldform
dilation 共用同一变换、连续谱的 Plancherel 二次型、单列零 Poisson 模式和
regular／exceptional 高度求和。

pin 有普通 primitive-character 大筛
[weightedPrimitiveSquareLedger_cell_largeSieve](https://github.com/subfish-zhou/goldbach-lean/blob/09b97db5764ade1246bfb77206baa1b124760958/MathlibNt/AnalyticNumberTheory/LargeSieve/PrimitiveGaussFareyExactBridge.lean)。
其实际 `primitiveGaussFareyCellFactor R L` 带 `R^2*log(R)` 损失；不能改写成
尖锐 `L+4R^2`。普通乘法大筛与完整 Weil 均不能替换 (24)。针对固定源码检索后，
未定位匹配上述 Kuznetsov／ABL／exceptional 归一化的供应者。

本轮没有建立对当前 restricted 手稿步骤的反例，也未确认某条当前经典引文为错。
以上是具体的供应者接口差异和未完成推导，不是宣称手稿步骤只剩机械翻译。

## 6. 验证证据与可接收范围

第二轮唯一一次新原版命令在 `2026-10-12T03:11:02.653589+00:00` 执行：

```text
/workspace/scratch/e8f85e58ac36/tooling/lean-4.33.0-rc1-linux/bin/lean --version
exit_code: 1
stderr: error: failed to locate application
```

同次只读诊断仍为数字 PID 的 `/proc/<pid>/exe` 返回 `EACCES`。没有提权重试、
修改编译器或绕过检查。无五模块 `.olean` 缓存或成功证明记录；P0 所存同 SHA
快照只匹配首轮静态报告。旧最后 CI run `38194578264` 的 job `114634325217`
经本轮只读查询仍是 `runner_id=0, runner_name="", steps=[]`，不能计为 Lean 失败
或成功，没有手动 dispatch／rerun。

验证器和审计导入清单都扩为七个模块，原有 gate 未放宽。实际执行的 source-only
检查、固定配置／基线内容核对及当前源码审查结果逐项保存在 `VERIFICATION.json`。
首轮 Python／workflow fixture 结果保留为历史记录，不当作本轮新的 Lean 结果。

| 层次 | 本轮状态 | 接收边界 |
|---|---|---|
| 通用 rough 删除误差与大模数误差 | 完整数学推导与 Lean 证明候选，未编译 | Part 3 后续 SW 证明使用前须过正常验证 |
| 原 admissibility 上 full auxiliary SW | 从显式小模数 SW 得出的条件证明候选，未编译 | 不能登记为无条件实际 SW 供应者 |
| 实际 rough `1`／Möbius 槽族 SW | 小 `q`、`k=1` 输入仍开放 | Part 3 负责继续证明；实际 chart/frequency 来源须保留 |
| restricted medium 与高模数上下源 | 未闭合 | Part 3 → Parts 4/5；Part 0 跟踪 |
| Y3–Y6 ordinary BV 实际实例 | 通用完整余项候选保留，policy cap 未取得 | Part 1 + Part 3 → Part 5 |
| one-long／two-long／低秩拼装 | 只保留已适用候选，未新增非法分支连接 | Part 3 → Parts 4/5 |

Part 0 接收固定提交、准确的未验证标记和剩余命题；正常环境恢复后，须在对应 SHA
的干净 checkout 运行现有完整验证器。本地目前是通过 GitHub 连接器取回的源码
快照，不能把其尚无 HEAD 的本地 Git 状态伪装成已验证 checkout。

Part 1 在实际实例化时仍须交付完整物理 modulus cap、带符号系数界、真实上下源
恒等式和 whole-box 因子分解许可。这个输入缺席不阻止本轮的通用解析推导。
`theta_*=599/1000`、当前 `K=8452171/1250000`、三个物理模数因子和共同完成相位
均未更改；所需最外层 signed 抵消仍留在未闭合的 medium 目标中。
