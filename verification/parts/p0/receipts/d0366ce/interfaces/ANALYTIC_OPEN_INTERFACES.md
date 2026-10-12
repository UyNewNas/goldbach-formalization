# P0 最终交接附页：P4-A / P5 仍开放的真实解析接口

## 结论与证据口径

**固定集成 `d0366ce64272e81faf6166a8a90050f56b328d38` 仍未闭合最终 `hLower` 和 `hUpper`。** 当前可复用的是已验证的条件式主桥、实际权到计数的误差桥、有限十一项账本及局部证书/上游 Rosser 组件；同一实际 `rho` 的 K 密度、完整当前 Chen 均值、解析 c 及最终上下界仍须真实供应。**P5 等待 P4-A 的共同实际权和 K 供应，并消费 P1/P2/P3 的对应输入；P5 无需等待 P4-B 的 RealB 专用上界。**

本附页只读该固定集成 SHA、其中归档的固定候选、既有台账与 intakes；没有运行 Lean、Lake、CI 或网络，没有更改仓库或其他 Part 分支。下列代码块明确区分三类：

| 标记 | 含义 |
|---|---|
| 已编译组件；源码签名 | 组件已有匹配验证记录，下面从固定真实源码抄完整声明头，便于保留通常数学记号；该代码块本身不是本轮新的编译器输出 |
| 编译器确认类型 | 逐字读取已保存的实际编译器记录；注明记录对应 SHA 和打印格式 |
| 仅源码候选 / 待证明规格 | 前者确有固定源但门未闭合，后者是先前共同接口单的目标，不是现有已证声明 |

除明确列出的上游命名空间外，源码签名保留原文件的 `namespace ImbalancedChen` 及其导入、`open Filter` / `open Topology` 上下文。提取仅去掉证明体，类型中的 `let`、隐式参数、数值、量词和假设均保留。

共同证明基线仍为 `1a80c1bcce67886f699d097fc37fd245cd3620bf`，手稿仍为 `ba6ec11d800eccc54406490631895e174de85766`。Lean 为 `leanprover/lean4:v4.33.0-rc1`，goldbach pin 为 `09b97db5764ade1246bfb77206baa1b124760958`。完整来源台账见 [docs/PART0_ROUND4_VERIFICATION.md](https://github.com/UyNewNas/goldbach-formalization/blob/d0366ce64272e81faf6166a8a90050f56b328d38/docs/PART0_ROUND4_VERIFICATION.md)、[verification/parts/p0/round3/ledger/MODULE_LEDGER.md](https://github.com/UyNewNas/goldbach-formalization/blob/d0366ce64272e81faf6166a8a90050f56b328d38/verification/parts/p0/round3/ledger/MODULE_LEDGER.md) 和 [docs/CHEN_175_BASELINE_INTERFACES.md](https://github.com/UyNewNas/goldbach-formalization/blob/d0366ce64272e81faf6166a8a90050f56b328d38/docs/CHEN_175_BASELINE_INTERFACES.md)。本附页不从本批 VE 的成功推导其他模块的验证状态。

### 已约定的生产供应位置

以下是首轮文件所有权的后续交付位置；本固定树中这些叶文件尚未存在。不能因有接口规格或归档候选而声称这些完成品已加入生产根。

| 所有者 | 计划路径（均相对仓库根） | 应交实际内容 |
|---|---|---|
| P4-A | `ImbalancedChen/CurrentPhysicalWeight.lean`、`ImbalancedChen/CurrentDensityBound.lean` | 与 P1 编译历史精确绑定的实际权、许可、支持和同 rho 的解析 K |
| P4-B | `ImbalancedChen/CurrentBadUpper.lean` | 消去真实供应前提的任意固定实 b 的 hUpper |
| P5 | `ImbalancedChen/CurrentChenMeanData.lean` | 完整实际下界泛函与 labelled source 的纯定义，先供 P2 消费 |
| P5 | `ImbalancedChen/CurrentPositiveFamilyUpper.lean`、`ImbalancedChen/CurrentRenewalSoundness.lean` | 实际非负 switched-family U*、H/h 与 renewal 数值证书的解析语义 |
| P5 | `ImbalancedChen/CurrentChenMean.lean`、`ImbalancedChen/CurrentChenLower.lean` | 完整当前十一项均值、解析 c 和无额外分析输入的 hLower |
| P2 | `ImbalancedChen/CurrentSameMaskV2.lean` | 唯一采用 mask 的真实数据定义与绑定 |
| P0 | `ImbalancedChen/CurrentMainComplete.lean` | 在证明体内调用真正闭合的 hLower / hUpper，复用现有条件式桥 |

纯定义层先固定再供其他 Part 导入；其文件中不能藏入待证均值或 K 的假设字段。最终公共导入与入口仍由 P0 维护。

## 1. 最终入口的完整真实输入

来源是 [ImbalancedChen/CurrentMainTheorem.lean](https://github.com/UyNewNas/goldbach-formalization/blob/d0366ce64272e81faf6166a8a90050f56b328d38/ImbalancedChen/CurrentMainTheorem.lean)。本文件及下节数值桥与已验父 `28fd630ef7cc38eba86beb6c0ba123336b5d05f2` 逐字节相同。父核心 run `38250288277` 的原始 artifact 已保存于 [verification/parts/p0/round4/prior-28fd630/core-artifact.zip](https://github.com/UyNewNas/goldbach-formalization/blob/d0366ce64272e81faf6166a8a90050f56b328d38/verification/parts/p0/round4/prior-28fd630/core-artifact.zip)；其中 `final-bridge.json` 有完整 `pp.all` 类型，明确保留名为 `hLower`、`hUpper` 的参数。本附页末尾原样附该完整类型，避免用“主定理已通过检查”混淆“主定理已消去分析假设”。

### 当前条件式主桥：完整源码签名

```lean
theorem current_theorem_1_1_of_manuscript_bounds
    {b : ℝ} (hbLower : (1 : ℝ) / 2 < b) (hbUpper : b < 1)
    (hLower : ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ N in Filter.atTop, Even N →
        (currentC - epsilon) * singularNormalization N ≤ (D12 N : ℝ))
    (hUpper : ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ N in Filter.atTop, Even N →
        (RealB b N : ℝ) ≤
          (currentK * Real.log (1 / b) + epsilon) *
            singularNormalization N) :
    ((currentC - currentK * Real.log (1 / b) : ℝ) : EReal) ≤
      Filter.liminf
        (fun N : ℕ =>
          (((RealDb b N : ℝ) / singularNormalization N : ℝ) : EReal))
        evenNatAtTop
```
`b` 是先固定的任意实数，范围为 `1/2 < b < 1`。两个分析输入均对每个正 `epsilon`、全部充分大偶数 `N` 有效；阈值可依赖先选定的参数。不能把它改为只对三个有理实例或一列偶数成立。

两个输入单独展开如下；它们就是当前主桥的实参类型，不引入新结构或类型类：

```lean
hLower : ∀ epsilon : ℝ, 0 < epsilon →
  ∀ᶠ N in Filter.atTop, Even N →
    (currentC - epsilon) * singularNormalization N ≤ (D12 N : ℝ)

hUpper : ∀ epsilon : ℝ, 0 < epsilon →
  ∀ᶠ N in Filter.atTop, Even N →
    (RealB b N : ℝ) ≤
      (currentK * Real.log (1 / b) + epsilon) * singularNormalization N
```
固定常数及尺度来自 [ImbalancedChen/CurrentNumericalTransfer.lean](https://github.com/UyNewNas/goldbach-formalization/blob/d0366ce64272e81faf6166a8a90050f56b328d38/ImbalancedChen/CurrentNumericalTransfer.lean)、[ImbalancedChen/SingularSeries.lean](https://github.com/UyNewNas/goldbach-formalization/blob/d0366ce64272e81faf6166a8a90050f56b328d38/ImbalancedChen/SingularSeries.lean)：

```lean
def currentK : ℝ := 8452171 / 1250000

def currentC : ℝ := 49044063 / 25000000

noncomputable def singularNormalization (N : ℕ) : ℝ :=
  singularSeries N * (N : ℝ) / (Real.log (N : ℝ)) ^ 2
```
其中 `currentK = 6.7617368`，`currentC = 1.96176252`。密度尺度为 `singularSeries N / log N`，源质量尺度为 `N / log N`，二者相乘才是计数尺度；奇异级数没有额外前置因子二。`D12` 排除余项 0、1，允许两个相同素因子；`RealB` 是 `RealDb` 在 `D12` 中的精确补集，`b<1` 时对应有序严格区域 `q^b < r ≤ q`。

### 各方应真正交出的终端规格

以下两条名称来自共同接口单；在本固定树中没有成为已证生产声明。它们是最终交付目标，不能把未证分析条件移到新参数上：

```lean
theorem current_D12_lower :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ N : ℕ in Filter.atTop, Even N →
        (currentC - epsilon) * singularNormalization N ≤ (D12 N : ℝ)

theorem current_realBad_upper
    {b : ℝ}
    (hbLower : (1 : ℝ) / 2 < b)
    (hbUpper : b < 1) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ N : ℕ in Filter.atTop, Even N →
        (RealB b N : ℝ) ≤
          (currentK * Real.log (1 / b) + epsilon) * singularNormalization N
```
P5 供应第一条，P4-B 供应第二条，P0 在完整入口的证明体内调用它们。原条件式桥继续保留。

## 2. P4-A：共同实际 rho 的来源、已证比较和缺失的 K

### 2.1 现有实际权，不能只交一个数字 K

已编译组件；下列定义和签名从固定真实源码提取。来源：[ImbalancedChen/ActualSmallRoughAttachment.lean](https://github.com/UyNewNas/goldbach-formalization/blob/d0366ce64272e81faf6166a8a90050f56b328d38/ImbalancedChen/ActualSmallRoughAttachment.lean)。这组定义是小素数 Rosser 权与真实 rough 系数的物理乘积附着。

```lean
def actualSmallRoughModuli (retainOdd : List ℕ → Bool)
    (N cap : ℕ) (w z : ℝ) : Finset ℕ :=
  smallRoughModuli (actualSmallRosserSupport N cap w)
    (fixedRoughSupport retainOdd N cap w z)

def actualSmallRoughRho (retainOdd : List ℕ → Bool)
    (N cap : ℕ) (w z L : ℝ) : ℕ → ℝ :=
  smallRoughRho (actualSmallRosserSupport N cap w)
    (fixedRoughSupport retainOdd N cap w z)
    (fixedRoughCoefficient retainOdd N cap w z)
    (actualSmallRosserMinus N cap w L) (actualSmallRosserPlus N cap w L)
```

```lean
theorem actualSmallRoughRho_majorant
    (retainOdd : List ℕ → Bool) (N cap : ℕ) (w z L : ℝ)
    (hL : 1 < L) (hwL : w ≤ L) (hwz : w ≤ z)
    (hzcap : z ≤ (cap : ℝ)) (n : ℤ) :
    actualSmallRoughIndicator N z n ≤
      physicalDivisorSum (actualSmallRoughModuli retainOdd N cap w z)
        (actualSmallRoughRho retainOdd N cap w z L) n.natAbs

theorem actualSmallRoughRho_abs_le_one
    (retainOdd : List ℕ → Bool) (N cap : ℕ) (w z L : ℝ) (q : ℕ) :
    |actualSmallRoughRho retainOdd N cap w z L q| ≤ 1

theorem actualSmallRoughRho_ne_zero_factors
    (retainOdd : List ℕ → Bool) (N cap : ℕ) (w z L : ℝ) {q : ℕ}
    (hq : actualSmallRoughRho retainOdd N cap w z L q ≠ 0) :
    ∃ a ∈ actualSmallRosserSupport N cap w,
      ∃ b ∈ fixedRoughSupport retainOdd N cap w z,
        q = a * b ∧ (a : ℝ) < L ∧
          fixedRoughCoefficient retainOdd N cap w z b ≠ 0
```
这些结果保留所有整数 `n : ℤ` 的 majorant（包含零与负数）、真实有限支撑和 `|rho|≤1`。显示 carrier 可能包含系数为零的项；物理 cutoff 应针对非零系数，不应无根据地加到整个显示 carrier 上。实际采用的历史 boxed compiler 若改变 rough 系数，须证明共同 carrier 上的逐系数对应/支配以及误差，不得把它直接视作另一棵 raw retention tree。

### 2.2 已编译的附着 reserve 比较

该定理没有 `hIntegral` 前提，但其结论右端仍含**同一政策的真实 raw density**；它没有把这项估成 `currentK`。完整源码签名如下：

```lean
theorem exists_actualSmallRoughRho_density_le_full_reserve
    (nu r eta epsilonMax : ℝ) (hnu : 0 < nu) (hr : 0 < r)
    (heta : 0 < eta) (hepsilonMax : 0 < epsilonMax) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ epsilon < 1 / 8 ∧
      epsilon < epsilonMax ∧ epsilon ^ 2 ≤ r ∧
      ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → Even N →
        ∀ cap : ℕ, (N : ℝ) ^ (nu * r) ≤ (cap : ℝ) →
          ∀ retainOdd : List ℕ → Bool,
            let w := (N : ℝ) ^ (nu * epsilon ^ 2)
            let z := (N : ℝ) ^ (nu * r)
            let L := (N : ℝ) ^ (nu * epsilon)
            physicalDensitySum (actualSmallRoughModuli retainOdd N cap w z)
                (actualSmallRoughRho retainOdd N cap w z L) ≤
              reciprocalTotientDensity (fixedRoughSupport retainOdd N cap 0 z)
                (fixedRoughCoefficient retainOdd N cap 0 z) +
                  eta * singularSeries N / Real.log (N : ℝ)
```
来源：[ImbalancedChen/ActualFirstExitDensityProjection.lean](https://github.com/UyNewNas/goldbach-formalization/blob/d0366ce64272e81faf6166a8a90050f56b328d38/ImbalancedChen/ActualFirstExitDensityProjection.lean)。特别注意量词是先选一个 `epsilon` 与 `N₀`，随后统一控制所有满足 cap 门的 `cap` 和所有 `retainOdd`；不能把该量词改成不相容的逐目标选权。

### 2.3 P4-A 固定候选：完整类型仍有真实供应输入

P4 证明源固定 SHA 为 `262f69822a386a9d44efc059bceba11049668d68`，最新交接为 `3d5dd058cf6bef5fe90719ee277580baf8b5bf41`。五个文件在集成树中只以台账源码快照保存，没有进入生产根。专项 run `38227776544` 在依赖构建阶段 1,800 秒超时；五个目标的编译、重放和所属声明公理门均未到达，没有可归属这些目标的 Lean 诊断，也没有匹配编译对象。

| Part | 真实候选文件 | 本批身份 |
|---|---|---|
| P4-A | `ActualUpperPolicyDensity.lean` | raw policy 与实际附着字典，源码候选 |
| P4-A | `UpperCoefficientPerturbation.lean` | coefficient perturbation / 支配，源码候选 |
| P4-A | `ActualUpperDensityAssembly.lean` | 全政策积分与数值输入的条件组装，源码候选 |
| P4-B | `RealPhysicalUpperWeightBridge.lean` | RealB / 实际物理权有限桥，源码候选 |
| P4-B | `RealUpperCountingAssembly.lean` | 同 rho 输入的最终上界条件组装，源码候选 |


### exists_actualSmallRoughRho_density_le_currentK_of_full_policy_limits

仅源码候选，未编译；完整声明头。来源：[verification/parts/p0/round3/ledger/snapshot-sources/ImbalancedChen/ActualUpperDensityAssembly.lean](https://github.com/UyNewNas/goldbach-formalization/blob/d0366ce64272e81faf6166a8a90050f56b328d38/verification/parts/p0/round3/ledger/snapshot-sources/ImbalancedChen/ActualUpperDensityAssembly.lean)
```lean
theorem exists_actualSmallRoughRho_density_le_currentK_of_full_policy_limits
    (nu sieveR epsilonMax rawBound : ℝ)
    (hnu : 0 < nu) (hr : 0 < sieveR) (hepsilonMax : 0 < epsilonMax)
    (retainOdd : ℝ → ℕ → List ℕ → Bool) (cap : ℕ → ℕ) (integral : ℝ → ℝ)
    (hcap : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      (N : ℝ) ^ (nu * sieveR) ≤ (cap N : ℝ))
    (hIntegral : ∀ epsilon : ℝ, 0 < epsilon → epsilon < epsilonMax →
      Tendsto (fun N : ℕ =>
        reciprocalTotientDensity
          (fixedRoughSupport (retainOdd epsilon N) N (cap N) 0
            ((N : ℝ) ^ (nu * sieveR)))
          (fixedRoughCoefficient (retainOdd epsilon N) N (cap N) 0
            ((N : ℝ) ^ (nu * sieveR))) *
          Real.log (N : ℝ) / singularSeries N)
        (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N})
        (𝓝 (integral epsilon)))
    (hCertificate : ∀ epsilon : ℝ, 0 < epsilon → epsilon < epsilonMax →
      integral epsilon ≤ rawBound)
    (hgap : rawBound < currentK) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ epsilon < 1 / 8 ∧
      epsilon < epsilonMax ∧ epsilon ^ 2 ≤ sieveR ∧
      ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → Even N →
        let w := (N : ℝ) ^ (nu * epsilon ^ 2)
        let z := (N : ℝ) ^ (nu * sieveR)
        let L := (N : ℝ) ^ (nu * epsilon)
        physicalDensitySum (actualSmallRoughModuli (retainOdd epsilon N) N (cap N) w z)
            (actualSmallRoughRho (retainOdd epsilon N) N (cap N) w z L) ≤
          currentK * (singularSeries N / Real.log (N : ℝ))
```
这里 `integral`、`retainOdd`、`cap` 都是参数，`hIntegral`、`hCertificate`、`hgap` 仍是输入。不能把“类型写出 currentK”接收为当前政策已经满足 K。还须固定当前完整历史 policy、证明真实全域积分极限、采用上界证书及两项实际 reserve、兑现参数和 cap 门。历史归一化若先用 `log D`，也必须完成到 `log N` 的实际系数转换。

### compiled_physicalDensity_le_currentK_of_raw_and_coefficient_budget

仅源码候选，未编译；完整声明头。来源：[verification/parts/p0/round3/ledger/snapshot-sources/ImbalancedChen/ActualUpperDensityAssembly.lean](https://github.com/UyNewNas/goldbach-formalization/blob/d0366ce64272e81faf6166a8a90050f56b328d38/verification/parts/p0/round3/ledger/snapshot-sources/ImbalancedChen/ActualUpperDensityAssembly.lean)
```lean
theorem compiled_physicalDensity_le_currentK_of_raw_and_coefficient_budget
    {N : ℕ} (hN : 2 ≤ N) {w : ℝ} {small rough : Finset ℕ}
    (hsmall : ∀ d ∈ small, SmallPrimeSupportedAt w d)
    (hrough : ∀ d ∈ rough, RoughPrimeSupportedAt w d)
    (compiled raw betaMinus betaPlus : ℕ → ℝ) (M rawBound compilerReserve : ℝ)
    (hminus : |reciprocalTotientDensity small betaMinus| ≤ M)
    (hplus : |reciprocalTotientDensity small betaPlus| ≤ M)
    (hraw : physicalDensitySum (smallRoughModuli small rough)
        (smallRoughRho small rough raw betaMinus betaPlus) ≤
      rawBound * (singularSeries N / Real.log (N : ℝ)))
    (hcompiler : M * reciprocalTotientDensity rough (fun d => |compiled d - raw d|) ≤
      compilerReserve * (singularSeries N / Real.log (N : ℝ)))
    (hbudget : rawBound + compilerReserve ≤ currentK) :
    physicalDensitySum (smallRoughModuli small rough)
        (smallRoughRho small rough compiled betaMinus betaPlus) *
        Real.log (N : ℝ) / singularSeries N ≤ currentK
```
boxed coefficient 分支还明确缺少 `hraw` 与 `hcompiler` 的实际供应。`hcompiler` 是小素数因子大小 M 乘以 rough 系数差的绝对 reciprocal-totient density，不能只比较符号和，也不能把 raw 与 compiled 放在不相同的未补零 carrier 上。

### 2.4 P4-A → P5 / P4-B 必须是同一次实际构造

P0 已约定的固定权模式，是对**已经具体定义并获许可的** `Q : ℕ → Finset ℕ`、`rho : ℕ → ℕ → ℝ` 证明：

```lean
∀ eta : ℝ, 0 < eta →
  ∀ᶠ N : ℕ in Filter.atTop, Even N →
    physicalDensitySum (Q N) (rho N) ≤
      (currentK + eta) * singularSeries N / Real.log (N : ℝ)
```
这只是消费规格；不是对任意 Q/rho 成立的断言。若精度会改变权，应改为共同接口单的按精度选权模式，并把 majorant、真实非零支持（含 `599/1000` 物理指数许可）、compiler 误差、密度和 P3 所需许可绑定到同一 `epsilon` 见证。P3 与 P5 的 signed PP、coprime correction、源质量估计必须直接消费该同一权，不能分别取两个存在见证。

本固定集成尚无计划的 `CurrentPhysicalWeight.lean` / `CurrentDensityBound.lean` 实际完成品；当前 P4 候选的这些输入也未被后续组件消去。P2 前 64 行证书中的有理 K 仅是已固定系数的数值实例，不提供这一解析密度结论。

## 3. P5：完整当前 Chen 均值与 c 的实际供应

### 3.1 已有实际权与载体

实际求和载体、当前权与 prime sum 不是抽象任意序列：

```lean
def chenAdditivePrimeCarrier (N : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range N).filter fun P => Nat.Prime P ∧ Nat.Coprime P N

def currentChenPairedWeight (n : ℕ) (N : ℝ) (E : ℕ × ℕ → Prop) : ℝ :=
  chenPairedElevenWeight n N (N ^ (417 / 5000 : ℝ)) (N ^ (19 / 125 : ℝ))
    (N ^ (59 / 250 : ℝ)) (N ^ (1 / 3 : ℝ)) E

def currentChenPairedPrimeSum (N : ℕ) (E : ℕ × ℕ → Prop) : ℝ :=
  ∑ P ∈ chenAdditivePrimeCarrier N, currentChenPairedWeight (N - P) (N : ℝ) E
```
`currentChenPairedPrimeSum` 的加法素数还要求与 N 互素，不能和 `D12` 的定义直接混写；其到 D12 的有限比较已由现有桥完成。第六项与第十一项末对必须使用同一采用区域 E，完整末对范围和 tuple 标签重数均需保留。

### currentChenPairedPrimeSum_eq_upsilon

已编译组件；完整源码签名，另有匹配 pp.all 记录。来源：[ImbalancedChen/CurrentChenMeanLedger.lean](https://github.com/UyNewNas/goldbach-formalization/blob/d0366ce64272e81faf6166a8a90050f56b328d38/ImbalancedChen/CurrentChenMeanLedger.lean)
```lean
theorem currentChenPairedPrimeSum_eq_upsilon (N : ℕ) (E : ℕ × ℕ → Prop) :
    currentChenPairedPrimeSum N E =
      3 * currentChenUpsilon1 N + currentChenUpsilon2 N - currentChenUpsilon3 N -
        currentChenUpsilon4 N + currentChenUpsilon5 N + currentChenUpsilon6 N E -
        2 * currentChenUpsilon7 N - currentChenUpsilon8 N - currentChenUpsilon9 N -
        currentChenUpsilon10 N - currentChenUpsilon11 N E
```
这个等式只把真实十一项排成账本。正号项 `1,2,5,6` 需要下界；负号项 `3,4,7,8,9,10,11` 需要上界；第一项系数是 3，第七项系数是 -2。U10/U11 若只供应真实合并证书，不能拆出没有证明的个别端点。

### currentChenPairedPrimeSum_ge_of_normalized_joint_last_bounds

已编译组件；完整源码签名，另有匹配 pp.all 记录。来源：[ImbalancedChen/CurrentChenMeanLedger.lean](https://github.com/UyNewNas/goldbach-formalization/blob/d0366ce64272e81faf6166a8a90050f56b328d38/ImbalancedChen/CurrentChenMeanLedger.lean)
```lean
theorem currentChenPairedPrimeSum_ge_of_normalized_joint_last_bounds
    (N : ℕ) (E : ℕ × ℕ → Prop)
    (b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀₁₁ delta : ℝ)
    (h₁ : (b₁ - delta) * singularNormalization N ≤ currentChenUpsilon1 N)
    (h₂ : (b₂ - delta) * singularNormalization N ≤ currentChenUpsilon2 N)
    (h₃ : currentChenUpsilon3 N ≤ (b₃ + delta) * singularNormalization N)
    (h₄ : currentChenUpsilon4 N ≤ (b₄ + delta) * singularNormalization N)
    (h₅ : (b₅ - delta) * singularNormalization N ≤ currentChenUpsilon5 N)
    (h₆ : (b₆ - delta) * singularNormalization N ≤ currentChenUpsilon6 N E)
    (h₇ : currentChenUpsilon7 N ≤ (b₇ + delta) * singularNormalization N)
    (h₈ : currentChenUpsilon8 N ≤ (b₈ + delta) * singularNormalization N)
    (h₉ : currentChenUpsilon9 N ≤ (b₉ + delta) * singularNormalization N)
    (h₁₀₁₁ : currentChenUpsilon10 N + currentChenUpsilon11 N E ≤
      (b₁₀₁₁ + 2 * delta) * singularNormalization N) :
    (3 * b₁ + b₂ - b₃ - b₄ + b₅ + b₆ - 2 * b₇ - b₈ - b₉ - b₁₀₁₁ -
      14 * delta) * singularNormalization N ≤ currentChenPairedPrimeSum N E
```
共同误差成本为 `14 * delta`，是绝对系数和。该有限组装保留全部逐项不等式；它不证明这些不等式在实际政策下成立，更没有证明十一项整体均值。

以上 `CurrentChenMeanLedger` 的 93 项与 `CurrentChenLowerScale` 的 5 项已有严格编译、原装重放、所属声明公理审计和完整 pp.all 输出，原件见 [verification/parts/p0/round2/p5-finite/compiler-types.json](https://github.com/UyNewNas/goldbach-formalization/blob/d0366ce64272e81faf6166a8a90050f56b328d38/verification/parts/p0/round2/p5-finite/compiler-types.json) 与 [verification/parts/p0/round2/p5-finite/receipt.json](https://github.com/UyNewNas/goldbach-formalization/blob/d0366ce64272e81faf6166a8a90050f56b328d38/verification/parts/p0/round2/p5-finite/receipt.json)。源码与已验父完全相同。本附页沿用这些已执行记录。

### 3.2 已有计数误差与因子四，不应重造或重复除四

已编译组件；完整源码签名：

```lean
theorem currentChenPairedPrimeSum_le_four_D12_add_error (N : ℕ)
    (E : ℕ × ℕ → Prop) (hN : 1 ≤ (N : ℝ))
    (hA : 1 < (N : ℝ) ^ (417 / 5000 : ℝ)) :
    currentChenPairedPrimeSum N E ≤ 4 * (D12 N : ℝ) +
      246 * ((N : ℝ) / ((N : ℝ) ^ (417 / 5000 : ℝ) - 1)) + 4

theorem eventually_currentChenPairedPrimeSum_sub_normalized_error_le_four_D12
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N : ℕ in atTop, ∀ E : ℕ × ℕ → Prop,
      currentChenPairedPrimeSum N E - epsilon * singularNormalization N ≤
        4 * (D12 N : ℝ)
```
来源：[ImbalancedChen/CurrentChenSummedBridge.lean](https://github.com/UyNewNas/goldbach-formalization/blob/d0366ce64272e81faf6166a8a90050f56b328d38/ImbalancedChen/CurrentChenSummedBridge.lean)。第二条在同一个充分大阈值后对任意 `E` 统一成立，因此 E 可以实际依赖 N。它已支付 squareful receiver 与单位余项造成的一侧计数误差；它没有提供权的均值下界。

```lean
theorem currentChen_four_currentC :
    4 * currentC = (49044063 : ℝ) / 6250000

theorem currentChen_lower_scale_of_equal_finite_budgets
    {N : ℕ} (E : ℕ × ℕ → Prop) {epsilon : ℝ}
    (hweight : (4 * currentC - 2 * epsilon) * singularNormalization N ≤
      currentChenPairedPrimeSum N E)
    (hcount : currentChenPairedPrimeSum N E -
      (2 * epsilon) * singularNormalization N ≤ 4 * (D12 N : ℝ)) :
    (currentC - epsilon) * singularNormalization N ≤ (D12 N : ℝ)
```
来源：[ImbalancedChen/CurrentChenLowerScale.lean](https://github.com/UyNewNas/goldbach-formalization/blob/d0366ce64272e81faf6166a8a90050f56b328d38/ImbalancedChen/CurrentChenLowerScale.lean)。完整均值所需系数是 **`4 * currentC = 49044063/6250000 = 7.84705008`**。当真实均值在损失 `2*epsilon` 下成立，再与已证 uniform-selector count-error 的 `2*epsilon` 实例合并，即可使用已有有限预算桥得到最终 `currentC-epsilon`。这个推导安排没有新的分析假设；待补的是前一不等式的真实生产者。

### 3.3 P5 应交的完整均值规格，当前仍未完成

共同接口单把唯一实际选择区域交由 P2 的 `CurrentSameMaskV2.lean` 定义，然后供 P5 消费：

```lean
currentPairedSelection : ℕ → (ℕ × ℕ → Prop)

theorem current_chen_paired_mean_lower :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ N : ℕ in Filter.atTop, Even N →
        (4 * currentC - epsilon) * singularNormalization N ≤
          currentChenPairedPrimeSum N (currentPairedSelection N)
```
**这是待证明规格，两个名字不能被当作本树已有值或定理。** 采用版本仍为 same-mask-v2、7/3、17,572 个原始行；本批 Prefix64 只核验 E0 的 `[0,64)`。还缺 E0 `[64,6091)` 与 E1 `[6091,17572)` 共 17,508 行，以及 saved-floor 语义、实际几何并域、历史合法性、完整积分到算术计数对应、Y6/Y11 同一 mask 和全误差总账。已证有限行序号覆盖/无重复不自动证明真实全局区域覆盖与无重计。

上下界实际积分泛函及原始端点、近似/编译 reserve 仍须 P1/P2/P5 对相同对象供应。若把泛函定义成证书端点，或用结构的一个字段直接假设均值达到 4c，都没有解决这一输入。

### 3.4 P5 所需的一般正 switched-family U* 独立于 P4-B

计划所有权是 P5 的 `CurrentPositiveFamilyUpper.lean`；该完成品当前不存在。对真实已获许可、标签/乘积重数保持、非负的 `weight` 和真实 `M`，它应把实际源质量与同 rho 的 K/PP 供应转为：

```lean
∀ J : ℝ, 0 ≤ J →
  (∀ eta : ℝ, 0 < eta →
    ∀ᶠ N : ℕ in Filter.atTop, Even N →
      (∑ m ∈ M N, weight N m) ≤
        (J + eta) * ((N : ℝ) / Real.log (N : ℝ))) →
  ∀ eta : ℝ, 0 < eta →
    ∀ᶠ N : ℕ in Filter.atTop, Even N →
      (∑ m ∈ M N,
        if m < N ∧ Nat.Prime (N - m) then weight N m else 0) ≤
          (currentK * J + eta) * singularNormalization N
```
此处 `M : ℕ → Finset ℕ`、`weight : ℕ → ℕ → ℝ` 应由真实 labelled source 定义（例如按乘积聚合时保留标签总权）；上述是共同接口单的消费模式，实际完整生产者仍须列出并兑现非负性、共同区间/加法相位、product scale、smoothing、primitive coprime 修正和小素数加数损失的许可。P3 交付的 signed PP 要在 sum 外取一次绝对值，且使用 P4-A 选出的同一实际 rho。J=0 也须成立。

每个当前 switched family 的实际源质量与许可由 P5 消去，再给出所需负号项上界；单独一个 K 数字或 RealB 上界不能替代这座 U* 桥。现有 P3 LongSlot / Normalization 可复用，但 remaining rough/prime、共同相位、Brun/Mellin、restricted medium、two-long 等实际供应并未因这两个模块通过而闭合。

因此真实依赖为 **P1/P2 的实际构造与证书 → P4-A 的同 rho K**，以及 **P4-A + P3 → P5 的 U* → 当前十一项均值 → c/hLower**。P4-B 另行给 RealB 专用 hUpper；没有 P4-B → P5 的等待边。

## 4. P5 新接收的 S1LowerRosser 到底解除什么

### 4.1 已编译、重放、全声明公理审计的实际节点

固定 P5 交接为 `7b1283e4a70874e4fb7004bafad0793069bdea71`。本批只是接收既有 goldbach pin 的 `MathlibNt.SieveTheory.LiLiuGoldbachS1LowerRosser`，没有新增 ImbalancedChen 生产证明。

| 对象 | 固定身份与范围 |
|---|---|
| 生产源码 SHA-256 | `c07c0704c975bef4d772090ce03d7536f28edd319c700c4d9feb27c9f111ef62` |
| 同一目标对象 SHA-256 | `005d9ac78bbd5e65386511bd975758f4fa8ed955e327c794569ab4a538be4988` |
| 直接导入 | `MathlibNt.SieveTheory.LiLiuGoldbachS1Carrier` |
| 实际严格编译 / stock replay / audit | 259.896 秒 / 95.498 秒 / 358.243 秒，全部 exit 0 |
| 所属声明 | 8，含 7 theorem 与 1 definition；private/generated 均在清单中 |
| 公理 | 仅 `Classical.choice`、`Quot.sound`、`propext` |
| 类型格式 | 8 项 actual explicit 与 raw Expr；不是 pp.all；一个 generated 默认类型有省略 |

来源：[verification/parts/p0/round4/intake/p5-intake/P5_FIXED_INTAKE.json](https://github.com/UyNewNas/goldbach-formalization/blob/d0366ce64272e81faf6166a8a90050f56b328d38/verification/parts/p0/round4/intake/p5-intake/P5_FIXED_INTAKE.json)、[docs/CHEN_P5_S1LOWERROSSER_HANDOFF.md](https://github.com/UyNewNas/goldbach-formalization/blob/d0366ce64272e81faf6166a8a90050f56b328d38/docs/CHEN_P5_S1LOWERROSSER_HANDOFF.md)。对象在严格编译输出、重放输入及 audit 直接导入之间的身份已绑定；8 项不属于新增自有根模块计数。该模块未进入当前主根依赖闭包，不能从本批主根或 VE CI 成功宣称覆盖；仍复用其独立生产者证据。

以下两条是**编译器确认类型**：从实际公开类型 JSON 的默认可读字段原样取出，完整 explicit 参数与 raw Expr 已在同一 [verification/parts/p5/round4/s1lowerrosser/public-theorem-types.json](https://github.com/UyNewNas/goldbach-formalization/blob/d0366ce64272e81faf6166a8a90050f56b328d38/verification/parts/p5/round4/s1lowerrosser/public-theorem-types.json) 保存。

```lean
MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachS1BoundingSieve_lowerErrSum_le_prefixSum :
∀ {N : ℕ} (hEven : Even N) {ε z : ℝ},
  0 ≤ ε →
    2 ≤ MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachS1Endpoint N ε →
      ∀ {D Q0 : ℕ},
        D ≤ Q0 + 1 →
          MathlibNt.SieveTheory.LinearSieve.lowerErrSum
              (MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachS1BoundingSieve N hEven ε z) D
              (MathlibNt.SieveTheory.LinearSieve.lowerRosserWeight
                (MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachS1ProdPrimes N z) D) ≤
            ∑ q ∈ Finset.Icc 1 Q0, MathlibNt.SieveTheory.BombieriVinogradov.standardPrimeAPPrefixMaxError N q
```

```lean
MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachS1_lowerRosser_mainTerm_sub_prefix_le :
∀ {N : ℕ} {ε z : ℝ},
  0 < ε →
    ε < 1 →
      Even N →
        2 ≤ MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachS1Endpoint N ε →
          2 ≤ z →
            ∀ {D Q0 : ℕ},
              (∀ p ∈ (MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachS1ProdPrimes N z).primeFactors,
                  p < D) →
                D ≤ Q0 + 1 →
                  MathlibNt.SieveTheory.BombieriVinogradov.trueLogarithmicIntegral
                          ↑(MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachS1Endpoint N ε) *
                        ∑ d ∈ (MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachS1ProdPrimes N z).divisors,
                          MathlibNt.SieveTheory.LinearSieve.lowerRosserWeight
                              (MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachS1ProdPrimes N z) D d /
                            ↑d.totient -
                      ∑ q ∈ Finset.Icc 1 Q0,
                        MathlibNt.SieveTheory.BombieriVinogradov.standardPrimeAPPrefixMaxError N q ≤
                    ↑(MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachS1
                        (MathlibNt.SieveTheory.LiLiuOnePlusOneNine.goldbachDifferenceCarrier N ε) N z)
```
第二条的右端是返回 `ℤ` 的真实 `goldbachS1` 计数转为 `ℝ`，不是新抽象均值。主项是实际严格端点 `m=ceil((1-epsilon)N)-1` 的 `trueLogarithmicIntegral m` 乘真实 lower Rosser/totient 有限和，误差仍为实际 AP 前缀误差和。

它解除 `S1BetaPaidLower` 调用该有限 Rosser 主项减 AP 误差定理的供应边，也解除密度分支对该模块的直接导入阻塞。它尚未支付 AP 误差的归一化损失，也未证明当前 Upsilon1 的 adopted L1、完整十一项均值、c 或 hLower。

### 4.2 InitialSource 与 InitialMean 的真实不同状态

| 节点 | 固定源 / 状态 |
|---|---|
| `CurrentChenInitialSource` | 源码 SHA-256 `4b11a63cc976a0866068337c12d616578dace6c80736574311f4cca13f7d8956`；producer strict / replay / audit 实际成功，8 条默认编译器类型无省略；旧 schema 缺 audit 导入目标对象前后绑定与完整 lineage，故仍是 `CANDIDATE_LEGACY_AUDIT_IMPORT_BINDING_PENDING` |
| `CurrentChenInitialMean` | 源码 SHA-256 `5358e4dbbda436b335620de19884624df3260386d5ab5e478a85f70599da6137`；固定源无匹配完成的编译/重放/审计，仍是仅源码候选 |

二者的固定源均归档于本 SHA 的 `verification/parts/p0/round3/ledger/snapshot-sources/ImbalancedChen/`，原 Part 源固定为 `bf54caeb5e708474cacefac13a171d307b4c64f2`。不能把 InitialSource 的旧成功套给 InitialMean，也不能把新 S1LowerRosser audit 自动补成旧 InitialSource 的对象绑定。

### currentChen_goldbachS1_le_sifted_add_primeFactors

源码签名；producer 有实际编译器类型，但消费者对象绑定门仍未齐。来源：[verification/parts/p0/round3/ledger/snapshot-sources/ImbalancedChen/CurrentChenInitialSource.lean](https://github.com/UyNewNas/goldbach-formalization/blob/d0366ce64272e81faf6166a8a90050f56b328d38/verification/parts/p0/round3/ledger/snapshot-sources/ImbalancedChen/CurrentChenInitialSource.lean)
```lean
theorem currentChen_goldbachS1_le_sifted_add_primeFactors
    (N : ℕ) (tau A z : ℝ) (hN : N ≠ 0) (htau : 0 ≤ tau) (hAz : A ≤ z) :
    (goldbachS1 (goldbachDifferenceCarrier N tau) N z : ℝ) ≤
      ((chenSiftedPrimeSource N A).card : ℝ) + (N.primeFactors.card : ℝ)
```

### eventually_currentChenUpsilon1_ge_initial_mean

仅源码候选，未编译；完整声明头。来源：[verification/parts/p0/round3/ledger/snapshot-sources/ImbalancedChen/CurrentChenInitialMean.lean](https://github.com/UyNewNas/goldbach-formalization/blob/d0366ce64272e81faf6166a8a90050f56b328d38/verification/parts/p0/round3/ledger/snapshot-sources/ImbalancedChen/CurrentChenInitialMean.lean)
```lean
theorem eventually_currentChenUpsilon1_ge_initial_mean
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N : ℕ in atTop, Even N →
      ((33 / 4 : ℝ) * Real.log 3 - epsilon) * singularNormalization N ≤
        currentChenUpsilon1 N
```
InitialMean 直接依赖 `MathlibNt.SieveTheory.LiLiuGoldbachS1BetaFixedNormalizedLower`。其 `(33/4)*log 3` 是独立第一项候选系数，不能改称 adopted L1，也不等于 4c。CurrentChenInitialSource 仍负责从 goldbach 差集筛到当前源的 primeFactors 删除成本。

### 4.3 真正的下一小批接口

既有 intake 保存的固定上游候选是 `MathlibNt.SieveTheory.LiLiuGoldbachS1MainMass`，唯一直接导入 `MathlibNt.SieveTheory.BombieriVinogradov`。源码 SHA-256 为 `4fdcdd6001278a1c7636a40ba8f2e2e6c685a20331a4b0c803c0146f516a4533`。本批未编译；以下从已有固定源码副本提取，不是编译器确认类型。

```lean
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

theorem goldbachS1_strictEndpoint_mainMass_lower (ε η : ℝ)
    (hε : 0 < ε) (hεu : ε < 1) (hη : 0 < η) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      let m : ℕ := ⌈(1 - ε) * (N : ℝ)⌉₊ - 1
      2 ≤ m ∧ m ≤ N ∧
        (1 - ε - η) * ((N : ℝ) / Real.log (N : ℝ)) ≤
          BombieriVinogradov.trueLogarithmicIntegral (m : ℝ)

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
```
固定上游来源：[LiLiuGoldbachS1MainMass.lean at goldbach pin](https://github.com/subfish-zhou/goldbach-lean/blob/09b97db5764ade1246bfb77206baa1b124760958/MathlibNt/SieveTheory/LiLiuGoldbachS1MainMass.lean)。既有 source binding 见 [verification/parts/p0/round4/intake/p5-intake/P5_FIXED_INTAKE.json](https://github.com/UyNewNas/goldbach-formalization/blob/d0366ce64272e81faf6166a8a90050f56b328d38/verification/parts/p0/round4/intake/p5-intake/P5_FIXED_INTAKE.json)。MainMass 之后仍须独立核验 S1BetaGeometry、S1BetaPaidLower 的 AP 支付和相关密度/尺度供应（含 `Bombieri1965Richert418Unconditional`，以及各分支的 Mertens / Jurkat–Richert / Suzuki），再到 `S1BetaFixedNormalizedLower` 与 CurrentChenInitialMean；接收 MainMass 本身也不完成这条链。

## 5. P4-B 的条件式上界候选与最终等待关系

为避免误认为已有 hUpper，下面保留实际 P4-B 候选的全部供应前提。它使用一个精度索引的 Q/rho，先固定 b、kappa、sieveExponent，再对 delta 取界。

### eventually_RealB_le_currentK_log_of_same_rho_inputs

仅源码候选，未编译；完整声明头。来源：[verification/parts/p0/round3/ledger/snapshot-sources/ImbalancedChen/RealUpperCountingAssembly.lean](https://github.com/UyNewNas/goldbach-formalization/blob/d0366ce64272e81faf6166a8a90050f56b328d38/verification/parts/p0/round3/ledger/snapshot-sources/ImbalancedChen/RealUpperCountingAssembly.lean)
```lean
theorem eventually_RealB_le_currentK_log_of_same_rho_inputs
    {b kappa sieveExponent : ℝ}
    (hb : 0 < b) (hb1 : b < 1) (hkappa : 0 < kappa)
    (hsieve : sieveExponent < 1)
    (Q : ℝ → ℕ → Finset ℕ) (rho : ℝ → ℕ → ℕ → ℝ)
    (hmajor : ∀ delta : ℝ, 0 < delta → ∀ᶠ N : ℕ in atTop, Even N → ∀ n : ℕ,
      (if Nat.Coprime n (sieveProduct N (Nat.ceil ((N : ℝ) ^ sieveExponent)))
        then (1 : ℝ) else 0) ≤ physicalDivisorSum (Q delta N) (rho delta N) n)
    (hdensity : ∀ delta : ℝ, 0 < delta → ∀ᶠ N : ℕ in atTop, Even N →
      physicalDensitySum (Q delta N) (rho delta N) ≤
        (currentK + delta) * (singularSeries N / Real.log (N : ℝ)))
    (hcoprime : ∀ delta : ℝ, 0 < delta → ∀ᶠ N : ℕ in atTop, Even N →
      |realPhysicalCoprimeCorrection b N (manuscriptHalfProductCutoff kappa N)
        (Q delta N) (rho delta N)| ≤ delta * singularNormalization N)
    (hdistribution : ∀ delta : ℝ, 0 < delta → ∀ᶠ N : ℕ in atTop, Even N →
      |realPhysicalDistributionError b N (manuscriptHalfProductCutoff kappa N)
        (Q delta N) (rho delta N)| ≤ delta * singularNormalization N) :
    ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ N : ℕ in atTop, Even N →
      (RealB b N : ℝ) ≤
        (currentK * Real.log (1 / b) + epsilon) * singularNormalization N
```
`hmajor`、`hdensity`、`hcoprime`、`hdistribution` 全部必须在同一个 `Q delta N` / `rho delta N` 上由实际生产者证明。若将它们变成结构的字段、类型类或直接命名成一个已证上界供应器，仍是等价未证输入，不能算最终 hUpper。

最终接收顺序及仍开放输入如下：

| 接收方 | 真正所需供应 | 当前最短缺口 |
|---|---|---|
| P4-A | P1 完整实际历史/支持/积分；P2 全上界证书；共同 compiler 与 reserve | 当前 policy、真实 integral、coefficient error 与同 rho K 尚未实例化证明；五个 P4 源仍候选 |
| P5 一般正 U* | P4-A 同一实际 rho 的 K / majorant / support；P3 对该实例的 signed PP / coprime / source 许可 | 只有局部已验分布组件；完整一般正上界桥尚未供应 |
| P5 完整 mean / c | U*；P1/P2 当前十一项实际积分与 adopted same-mask-v2；上游 S1 链 | 全实际逐项界、采用 L1、完整 mask/区域与误差账本仍缺 |
| P5 hLower | 完整实际 mean；已证 uniform-selector count-error 与 factor-four 有限预算桥 | 后两者可复用，真实 mean 尚缺；不等待 P4-B |
| P4-B hUpper | 同 rho K 与 P3 对真实 RealB 半乘积源的误差/质量 | 条件组装候选未验证且供应前提未消去 |
| P0 完整最终入口 | 无附加分析假设的 hLower 与 hUpper | 两条终端真实供应未齐，现有条件桥保持条件式 |

P0 应接收固定提交或补丁，并记录实际源、对象、完整类型及门结果；新集成的主根验证只能确认当次进入依赖闭包的对象，不能替代候选模块显式三门，也不能把已经成功的局部数值组件升级为 K/c 的完整分析证明。

## 附录 A. 已有主桥的原始编译器完整类型

**编译器确认类型；复用父 SHA，不是本轮重跑。** 原件来自父 `28fd630ef7cc38eba86beb6c0ba123336b5d05f2` 的完整 core artifact；当前主桥源码逐字节相同。Artifact SHA-256 是 `6927d09d7e2b4cd7dd201f21169c07111ff4325f77478682f5c316f551940e42`；`final-bridge.json` 成员 SHA-256 为 `3cb352de6e0bf32a03af96524e09810c48e63b0dd73fa07f3020c67a9d0e1ea9`。打印格式是 `pp.all`，未含省略标记；公理仅标准三项。

成员路径：`goldbach-formalization/goldbach-formalization/.lake/part0-round3-types/20261012T124709693564Z/final-bridge.json`。

```lean
ImbalancedChen.current_theorem_1_1_of_manuscript_bounds :
∀ {b : Real}
  (hbLower :
    @LT.lt.{0} Real Real.instLT
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
        (@OfNat.ofNat.{0} Real (nat_lit 2)
          (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))
      b)
  (hbUpper : @LT.lt.{0} Real Real.instLT b (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
  (hLower :
    ∀ (epsilon : Real),
      @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) epsilon →
        @Filter.Eventually.{0} Nat
          (fun (N : Nat) =>
            @Even.{0} Nat instAddNat N →
              @LE.le.{0} Real Real.instLE
                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) ImbalancedChen.currentC
                    epsilon)
                  (ImbalancedChen.singularNormalization N))
                (@Nat.cast.{0} Real Real.instNatCast (ImbalancedChen.D12 N)))
          (@Filter.atTop.{0} Nat Nat.instPreorder))
  (hUpper :
    ∀ (epsilon : Real),
      @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) epsilon →
        @Filter.Eventually.{0} Nat
          (fun (N : Nat) =>
            @Even.{0} Nat instAddNat N →
              @LE.le.{0} Real Real.instLE (@Nat.cast.{0} Real Real.instNatCast (ImbalancedChen.RealB b N))
                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                  (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) ImbalancedChen.currentK
                      (Real.log
                        (@HDiv.hDiv.{0, 0, 0} Real Real Real
                          (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) b)))
                    epsilon)
                  (ImbalancedChen.singularNormalization N)))
          (@Filter.atTop.{0} Nat Nat.instPreorder)),
  @LE.le.{0} EReal (@Preorder.toLE.{0} EReal (@PartialOrder.toPreorder.{0} EReal instPartialOrderEReal))
    (Real.toEReal
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) ImbalancedChen.currentC
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) ImbalancedChen.currentK
          (Real.log
            (@HDiv.hDiv.{0, 0, 0} Real Real Real
              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
              (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) b)))))
    (@Filter.liminf.{0, 0} EReal Nat
      (@ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} EReal
        (@ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} EReal
          (@CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} EReal instCompleteLinearOrderEReal)))
      (fun (N : Nat) =>
        Real.toEReal
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@Nat.cast.{0} Real Real.instNatCast (ImbalancedChen.RealDb b N)) (ImbalancedChen.singularNormalization N)))
      ImbalancedChen.evenNatAtTop)
```
## 附录 B. 本页直接读取的主要源码身份

下表 SHA-256 为本次从集成固定 Git 对象重算。候选的归档目录不能视作生产 import；其编译状态以前文为准。

| 固定 SHA 内路径 | SHA-256 |
|---|---|
| [ImbalancedChen/CurrentMainTheorem.lean](https://github.com/UyNewNas/goldbach-formalization/blob/d0366ce64272e81faf6166a8a90050f56b328d38/ImbalancedChen/CurrentMainTheorem.lean) | `68a2a3aad8ccdc73ed8e5076e31b9984bc659c307d71150920a71b5fc98f067d` |
| [ImbalancedChen/CurrentNumericalTransfer.lean](https://github.com/UyNewNas/goldbach-formalization/blob/d0366ce64272e81faf6166a8a90050f56b328d38/ImbalancedChen/CurrentNumericalTransfer.lean) | `acc924036cb6ca73ef660c632d5577462ba5c69b8b5600aef63255264c3a270a` |
| [ImbalancedChen/CurrentChenSummedBridge.lean](https://github.com/UyNewNas/goldbach-formalization/blob/d0366ce64272e81faf6166a8a90050f56b328d38/ImbalancedChen/CurrentChenSummedBridge.lean) | `e7897e67a0a51db8e2d0dc410a1240dea62774f5b94782bc30ddf9055a7be832` |
| [ImbalancedChen/CurrentChenMeanLedger.lean](https://github.com/UyNewNas/goldbach-formalization/blob/d0366ce64272e81faf6166a8a90050f56b328d38/ImbalancedChen/CurrentChenMeanLedger.lean) | `30597d5f381031fc7d7e794fe105a11d6981053b34a1406d46f40bf7840dc0c8` |
| [ImbalancedChen/CurrentChenLowerScale.lean](https://github.com/UyNewNas/goldbach-formalization/blob/d0366ce64272e81faf6166a8a90050f56b328d38/ImbalancedChen/CurrentChenLowerScale.lean) | `cea233e4897e4f550760ca82eba84e6ca9254593a8cbba030f22940e3086ab13` |
| [ImbalancedChen/ActualSmallRoughAttachment.lean](https://github.com/UyNewNas/goldbach-formalization/blob/d0366ce64272e81faf6166a8a90050f56b328d38/ImbalancedChen/ActualSmallRoughAttachment.lean) | `a7b17e728cb6ffe70e3b60c72f1a5d6febd38b12bf208f808a13b748a2da2625` |
| [ImbalancedChen/ActualFirstExitDensityProjection.lean](https://github.com/UyNewNas/goldbach-formalization/blob/d0366ce64272e81faf6166a8a90050f56b328d38/ImbalancedChen/ActualFirstExitDensityProjection.lean) | `7318f2bcd426b4101a7fc3d9a7a3376f695b030729bcfcf68515b0bef1a0c603` |
| [verification/parts/p0/round3/ledger/snapshot-sources/ImbalancedChen/ActualUpperDensityAssembly.lean](https://github.com/UyNewNas/goldbach-formalization/blob/d0366ce64272e81faf6166a8a90050f56b328d38/verification/parts/p0/round3/ledger/snapshot-sources/ImbalancedChen/ActualUpperDensityAssembly.lean) | `241eaf65d39385e9f556a80184b25b0b2c2f67503922ec03f6a55b15c646ef3d` |
| [verification/parts/p0/round3/ledger/snapshot-sources/ImbalancedChen/ActualUpperPolicyDensity.lean](https://github.com/UyNewNas/goldbach-formalization/blob/d0366ce64272e81faf6166a8a90050f56b328d38/verification/parts/p0/round3/ledger/snapshot-sources/ImbalancedChen/ActualUpperPolicyDensity.lean) | `16d81ee162d9ed2a5efad703c9a900b2c5ada622b2613472f70eaef4cbd02ae6` |
| [verification/parts/p0/round3/ledger/snapshot-sources/ImbalancedChen/UpperCoefficientPerturbation.lean](https://github.com/UyNewNas/goldbach-formalization/blob/d0366ce64272e81faf6166a8a90050f56b328d38/verification/parts/p0/round3/ledger/snapshot-sources/ImbalancedChen/UpperCoefficientPerturbation.lean) | `59b45cfb13444beee297beec05b6d2153d7207db4f9bd96a8652260eaa57bcef` |
| [verification/parts/p0/round3/ledger/snapshot-sources/ImbalancedChen/RealPhysicalUpperWeightBridge.lean](https://github.com/UyNewNas/goldbach-formalization/blob/d0366ce64272e81faf6166a8a90050f56b328d38/verification/parts/p0/round3/ledger/snapshot-sources/ImbalancedChen/RealPhysicalUpperWeightBridge.lean) | `f82e567435a61125c6972da1f2c1430ff946bbd44bd9b5538bd9a6003382ea9d` |
| [verification/parts/p0/round3/ledger/snapshot-sources/ImbalancedChen/RealUpperCountingAssembly.lean](https://github.com/UyNewNas/goldbach-formalization/blob/d0366ce64272e81faf6166a8a90050f56b328d38/verification/parts/p0/round3/ledger/snapshot-sources/ImbalancedChen/RealUpperCountingAssembly.lean) | `56bab762d3f765f5080a441910a8696e297bcd72801e13f4338b0ed7142a9a96` |
| [verification/parts/p0/round3/ledger/snapshot-sources/ImbalancedChen/CurrentChenInitialSource.lean](https://github.com/UyNewNas/goldbach-formalization/blob/d0366ce64272e81faf6166a8a90050f56b328d38/verification/parts/p0/round3/ledger/snapshot-sources/ImbalancedChen/CurrentChenInitialSource.lean) | `4b11a63cc976a0866068337c12d616578dace6c80736574311f4cca13f7d8956` |
| [verification/parts/p0/round3/ledger/snapshot-sources/ImbalancedChen/CurrentChenInitialMean.lean](https://github.com/UyNewNas/goldbach-formalization/blob/d0366ce64272e81faf6166a8a90050f56b328d38/verification/parts/p0/round3/ledger/snapshot-sources/ImbalancedChen/CurrentChenInitialMean.lean) | `5358e4dbbda436b335620de19884624df3260386d5ab5e478a85f70599da6137` |

本页所有“待证明规格”只作已约定接口说明；没有在仓库中新增 Lean 声明、未证包装或任何替代证明机制。
