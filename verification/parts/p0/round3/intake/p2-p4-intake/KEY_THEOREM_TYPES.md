# 本次可转交的关键完整定理类型

## 编译器确认的 P2 新模块

以下使用源码的常规 Lean 记法，保留全部量词、参数和假设；对应实际 `pp.all` 与 `readable_type` 字段完整保存在 `p2/COMPILER_TYPES_NEW.md` 和 `p2/compiler-confirmed-new-declarations.json`。这些字段已与固定 SHA 的 CI 输出逐条核对。

```lean
namespace ImbalancedChen.Certificates.PairedV2

theorem e0GeometryCheck_sound {i j : ℕ} {Z : ℚ}
    (hcheck : e0GeometryCheck i j Z = true) : E0Geometry i j Z

theorem E0Geometry.residual_bound {i j : ℕ} {Z : ℚ}
    (hg : E0Geometry i j Z) {t u : ℝ}
    (ht : (tLower i : ℝ) ≤ t) (hu : (uLower j : ℝ) ≤ u) :
    (57 / 64 : ℝ) - (5 / 2) * t - u ≤ 2 * (a : ℝ)

theorem E0Geometry.fibre_argument {i j : ℕ} {Z : ℚ}
    (hg : E0Geometry i j Z) {t u z w : ℝ}
    (hs : openFibreSupport i j Z t u z w) :
    (a : ℝ) < w ∧ w < z ∧ z < u ∧ u < (h : ℝ) ∧
      (h : ℝ) < t ∧ t < (d : ℝ) ∧
      (7 / 3 : ℝ) ≤ (1 - t - u - z - w) / z

theorem E0Geometry.fibre_nonempty {i j : ℕ} {Z : ℚ}
    (hg : E0Geometry i j Z) :
    ∃ t u z w : ℝ, openFibreSupport i j Z t u z w

namespace Prefix4

open MeasureTheory Set
open scoped BigOperators Interval

theorem certificates_checked (i : Fin 4) : (certificates i).check = true

theorem geometry_checked (i : Fin 4) :
    E0Geometry (rowIndices i).1 (rowIndices i).2 (rowZ i)

theorem certificate_inputs (i : Fin 4) :
    (certificates i).K = K ∧ (certificates i).a = a ∧
      (certificates i).tl = tLower (rowIndices i).1 ∧
      (certificates i).tr = tUpper (rowIndices i).1 ∧
      (certificates i).ul = uLower (rowIndices i).2 ∧
      (certificates i).ur = uUpper (rowIndices i).2 ∧
      (certificates i).Z = rowZ i

theorem fibre_argument (i : Fin 4) {t u z w : ℝ}
    (hs : openFibreSupport (rowIndices i).1 (rowIndices i).2 (rowZ i) t u z w) :
    (a : ℝ) < w ∧ w < z ∧ z < u ∧ u < (h : ℝ) ∧
      (h : ℝ) < t ∧ t < (d : ℝ) ∧
      (7 / 3 : ℝ) ≤ (1 - t - u - z - w) / z

theorem fibre_nonempty (i : Fin 4) :
    ∃ t u z w : ℝ,
      openFibreSupport (rowIndices i).1 (rowIndices i).2 (rowZ i) t u z w

theorem rowIntegral_eq_certificate (i : Fin 4) :
    rowIntegral i = pairedLocalIntegral ((certificates i).K : ℝ)
      (certificates i).a (certificates i).tl (certificates i).tr
      (certificates i).ul (certificates i).ur (certificates i).Z

theorem integral_semantics :
    integral = ((K : ℝ) / 80) * ∑ i : Fin 4,
      ∫ t in (tLower (rowIndices i).1 : ℝ)..(tUpper (rowIndices i).1 : ℝ),
      ∫ u in (uLower (rowIndices i).2 : ℝ)..(uUpper (rowIndices i).2 : ℝ),
      ∫ z in (a : ℝ)..(rowZ i : ℝ), ∫ w in (a : ℝ)..z,
        1 / (t * u * z ^ 2 * w)

theorem lower_sum : (∑ i : Fin 4, (certificates i).lower) = lowerBound

theorem upper_sum : (∑ i : Fin 4, (certificates i).upper) = upperBound

theorem integral_bounds :
    (lowerBound : ℝ) ≤ integral ∧ integral ≤ (upperBound : ℝ)

theorem integral_pos : 0 < integral

end Prefix4
end ImbalancedChen.Certificates.PairedV2
```

字面常数保持 `lowerBound = 12676565261567/100000000000000000000`、`upperBound = 12676572571081/100000000000000000000`。这些声明的证明均没有假定期望积分值。几何通用定理的 `E0Geometry` 是显式有限端点条件，四行实例由 `geometry_checked` 无额外假设提供。

## P4 固定候选：完整源码类型，尚未编译器确认

完整五模块的 53 个源码签名在 `p4/SOURCE_THEOREM_TYPES.md`。下面给出仍需真实供应者的最终 same-rho 条件接口；没有将它标为新无条件 hUpper。

```lean
namespace ImbalancedChen

open Filter Topology

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

end ImbalancedChen
```

该候选固定源码 SHA256 为 `56bab762d3f765f5080a441910a8696e297bcd72801e13f4338b0ed7142a9a96`。四个实际输入中的每一个仍必须由真实同一权供应。局部有限积分、有限权重代数或旧根 CI 成功不能替代这些输入。
