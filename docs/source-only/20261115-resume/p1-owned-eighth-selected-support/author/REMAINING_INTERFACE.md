# savingMiddle 之后仍需的真实接口

本轮的最小新增是原稿 §3 的 actual owned terminal full/selected square support。以下不是新 Lean predicate 或 conditional wrapper，而是说明现有已读源不能自动完成的后续步骤。

## 同一个实际系数先过整盒接口

原对象为 `full87PhysicalRhoChange r n e q om N cap w z L`，即原 sixth-policy 与原 eighth-policy 的两个零延拓物理系数之差。它保留 sign-selected small beta、全部 terminal primes 和 owned occurrence multiplicity。原 `SignedSharpReceiver.full87_owned_signed_sharp_callsite` 已给 exact finite equality；本轮不重写。

原稿要求在固定全局历史、正 rough cutoff、几何余量与 fine width 之后，对每个所需 U 构造实际整盒分组。组系数应分别只依赖 q1、q2、q3，并一有界；小 beta 按原严格 small/rough 分离进入第三组；原 repeated-label factorial 与恢复标量各计一次。分组可依赖盒/U/N 的端点，不能依赖盒内某个素数 tuple 或外层 HB 变量，也不能随 progression error 的符号换系数。

新候选只证明**每个实际词**满足同一 selected-cap 的几何前置条件。它还没有给同一 fine-label 盒全部点的统一 cap/mask/历史值，也没有证明端点提升后的同系数独立展开。

实际已读的 `P4AFull87TaggedAtomValue`：

- `fibre_scalar:45–49` 要求 `label tag N tau d = label tag N tau e`，其中 label 包含整个历史 tag；
- `original_factorial:54–64` 的左边仍是 `∑ ps, coefficient ... ps.prod * E ps.prod`，系数没有被取出；
- `actual_union_rho:68–79` 绑定它自己的原 union compiled rho，不是一个与历史 saving Δrho 已证明相等的声明。

因而“已有 factorial / fibre_scalar import”不能支付独立整盒重构。若采用原好盒与坏盒分拆，必须同时写出**本实际 Δrho**的 exact good-box identity 和 residual coefficient；然后从真实 AP/count 输入支付后者在 `sharpPrimeError N` 下的费用。现有 `CompilerPhysicalPayment.exists_actual_payment_with_inherited_remainder` 控制 reciprocal-totient mass、density 和其 mean-scale 规范化，并未在本实际 Δrho 上给该 signed-error 转移。一个未来使用 Brun–Titchmarsh 的真实转移或许可行，但本包没有加入假定它已成立的包装。

这首先是同原系数的构造/接线义务；不能仅凭名字判成原稿分析定理为假，也不能据当前源码字段缺少就宣称原始数学不成立。

## 真正的 restricted-medium 分析输入

`Part3DistributionTargets.lean:126–162` 已给以下原目标类型（此处引用已有定义，不新增声明）：

```lean
def RestrictedMediumTarget {ι : Type*} (F : ι → MediumAtom) : Prop :=
  ∀ A : ℝ, 0 < A → ∃ C : ℝ, 0 < C ∧ ∃ x0 : ℝ, 1 < x0 ∧
    ∀ i : ι, x0 ≤ (F i).scale →
      ‖(F i).signedError‖ ≤ C * (F i).scale / (Real.log (F i).scale) ^ A

def RestrictedMediumObligation {ι : Type*} (F : ι → MediumAtom)
    (B C0 : ℕ) (σ κ c0 : ℝ) : Prop :=
  0 < σ → σ < 1 / 100 → 0 < c0 → 0 ≤ κ → κ ≤ σ / 100 →
  (∀ i : ι, MediumAdmissible B σ κ c0 (F i)) →
  UniformAuxiliarySW F C0 → RestrictedMediumTarget F
```

实际待构造的 F 必须包括同一个原目标 N、原 HB chart、local-scale、U/V 与该 Δrho 整盒的三个 modulus 因子。四条中段大小约束仍是该定义的真约束：

```text
Q1 < U * x^(-σ)
U^2 * Q2 * Q3^2 < x^(1-8σ)
N^(7/32) * U * Q1 * Q2^5 * Q3^2 < x^(2-15σ)
U^(1+2*(7/32)) * Q1 * Q2^(5-2*(7/32)) * Q3^(2+2*(7/32))
  < x^(2-15σ)
```

这里 x=U*V，原 residue 的绝对值为 N，并保留 c0*x ≤ N ≤ x^(1+κ)。不能把 N 的 7/32 因子删掉。alpha 是真实 rough HB 单槽，beta 是原 complement divisor-bounded 系数，三个 gamma 对其各自变量一有界且与 residue 互素。`UniformAuxiliarySW` 的常数要在整个实际家族上统一，不能按一个 chart/tuple 单独选阈值。

当前 source-only `RestrictedMediumObligation` 是**定义**，没有凭这名字得到分析付款。J/native6 或 Weil 某条子路径的局部结果只有在它的最终声明实际产出上述族的估计并保持原参数、系数、标量费用后才可接到这里。本包未审计那条分析全图，也未把当前远程局部 success 认作 fullproof。

## 不可混用的末端 PP 合同

同文件 187–193 的原 type 为：

```lean
def UniformPrimeProductTarget {ι : Type*} (k : ℕ) (cap : ℕ → ℕ)
    (Q : ℕ → Finset ℕ) (rho : ℕ → ℕ → ℝ)
    (W : (N : ℕ) → ι → (Fin k → Fin (cap N + 1)) → ℝ) : Prop :=
  ∀ A : ℝ, 0 < A → ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ,
    ∀ N : ℕ, N0 ≤ N → Even N → ∀ i : ι,
      |primeProductSignedError k (cap N) N (Q N) (rho N) (W N i)| ≤
        C * (N : ℝ) / (Real.log (N : ℝ)) ^ A
```

若通过 singleton smoothing/HB 付款，原 prime enumeration cap 是 2N，physical target 仍是 N；W 应是原许可的 singleton family，chart cutoff、K/kappa 的预 N 选择仍取自原 supplier。对最终 rectangular `Params.rho` 已有的 HB identity/roughPrimeReserve=0，不能无同系数证明转给历史 Δrho。lower ALL16 的 `jointPresievedSigma` 也不能因同 import cone 就代入 upper 或 Δrho。

因此 savingMiddle 剩余的数学付款包含真实 restricted-medium 分析结论及其实际族接线；它不等价于一个量词改写或归一化简化。这里没有给原估计的反例。旧 full-union support obstruction 已有独立原像，且不适用于此原 active owned saving；本轮不重复其证明或将它错误扩张。
