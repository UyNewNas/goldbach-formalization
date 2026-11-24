import ImbalancedChen.Part3HeathBrownThree
import ImbalancedChen.Part3PrimeProductVonMangoldt

/-!
# The Heath--Brown coefficient expansion on actual labelled products

Each original coordinate gets its own real cutoff and one independent
Heath--Brown order. All fibres still use the original complete product.
The proper-prime-power union residual has the same original arithmetic
kernel and occurs once.
-/

namespace ImbalancedChen.Part3

noncomputable section

open Classical Finset
open scoped ArithmeticFunction ArithmeticFunction.zeta BigOperators

/-- The three signed coefficients of the original Heath--Brown formula. -/
def heathBrownThreeTerm (z : ℝ) (j : Fin 3) (n : ℕ) : ℝ :=
  let M := heathBrownTruncatedMoebius z
  ![3 * (M * ArithmeticFunction.log) n,
    -3 * (M^2 * (ζ : ArithmeticFunction ℝ) * ArithmeticFunction.log) n,
    (M^3 * (ζ : ArithmeticFunction ℝ)^2 * ArithmeticFunction.log) n] j

theorem sum_heathBrownThreeTerm (z : ℝ) (n : ℕ) :
    (∑ j : Fin 3, heathBrownThreeTerm z j n) = heathBrownThree z n := by
  rw [Fin.sum_univ_three]
  simp [heathBrownThreeTerm, heathBrownThree, sub_eq_add_neg]

/-- The exact coefficient of one choice of orders on all original
coordinates. The cutoffs depend only on the supplied original scales. -/
def labelledHeathBrownOrderMass (k P : ℕ) (R : Fin k → ℝ)
    (W : (Fin k → Fin (P + 1)) → ℝ) (j : Fin k → Fin 3) : ℕ → ℂ :=
  finiteProductMass univ labelledProduct (fun t =>
    ((W t * ∏ i : Fin k,
      heathBrownThreeTerm ((2 * R i) ^ (1 / 3 : ℝ)) (j i) (t i).val /
        Real.log (t i).val : ℝ) : ℂ))

private theorem labelled_weight_sum_orders {k P : ℕ} (R : Fin k → ℝ)
    (hR : ∀ i, 0 ≤ R i) (t : Fin k → Fin (P + 1))
    (ht : ∀ i, ((t i).val : ℝ) ≤ 2 * R i) :
    labelledVonMangoldtWeight t =
      ∑ j : Fin k → Fin 3, ∏ i : Fin k,
        heathBrownThreeTerm ((2 * R i) ^ (1 / 3 : ℝ)) (j i) (t i).val / Real.log (t i).val := by
  have H (i : Fin k) : vonMangoldtOverLog (t i).val =
      ∑ j : Fin 3, heathBrownThreeTerm ((2 * R i) ^ (1 / 3 : ℝ)) j (t i).val / Real.log (t i).val := by
    rw [vonMangoldtOverLog, heathBrown_three_at_original_scale (hR i) (ht i),
      ← sum_div, sum_heathBrownThreeTerm]
  unfold labelledVonMangoldtWeight
  simp only [H]
  rw [prod_univ_sum (fun _ : Fin k => (univ : Finset (Fin 3)))
    (fun i j => heathBrownThreeTerm ((2 * R i) ^ (1 / 3 : ℝ)) j (t i).val / Real.log (t i).val),
    Fintype.piFinset_univ]

/-- The replacement holds fibrewise on every complete product, including
all labels, coincidences and repeated prime coordinates. -/
theorem labelledVonMangoldtProductMass_eq_sum_heathBrownOrders (k P : ℕ) (R : Fin k → ℝ)
    (W : (Fin k → Fin (P + 1)) → ℝ) (hR : ∀ i, 0 ≤ R i)
    (hW : ∀ t, W t ≠ 0 → ∀ i, ((t i).val : ℝ) ≤ 2 * R i) (b : ℕ) :
    labelledVonMangoldtProductMass k P W b =
      ∑ j : Fin k → Fin 3, labelledHeathBrownOrderMass k P R W j b := by
  unfold labelledVonMangoldtProductMass labelledHeathBrownOrderMass finiteProductMass
  rw [sum_comm]
  apply sum_congr rfl
  intro t _
  by_cases hb : labelledProduct t = b
  · simp only [if_pos hb]
    by_cases hw : W t = 0
    · simp only [hw, zero_mul, Complex.ofReal_zero, sum_const_zero]
    rw [labelled_weight_sum_orders R hR t (hW t hw), mul_sum, Complex.ofReal_sum]
  · simp only [if_neg hb, sum_const_zero]

/-- The original signed prime-product error is the exact finite sum of
the order cells, with one proper-prime-power residual and the unchanged
primitive mean kernel. -/
theorem primeProductSignedError_eq_heathBrownOrders_sub_properPower
    (k P N : ℕ) (Q B : Finset ℕ) (ρ : ℕ → ℝ)
    (R : Fin k → ℝ) (W : (Fin k → Fin (P + 1)) → ℝ)
    (hB : ∀ t ∈ labelledPrimeTuples k P, W t ≠ 0 → labelledProduct t ∈ B)
    (hR : ∀ i, 0 ≤ R i)
    (hW : ∀ t, W t ≠ 0 → ∀ i, ((t i).val : ℝ) ≤ 2 * R i) :
    (primeProductSignedError k P N Q ρ W : ℂ) =
      (∑ j : Fin k → Fin 3, finiteProductSignedError B Q N
        (fun q => (ρ q : ℂ)) (labelledHeathBrownOrderMass k P R W j)) -
      finiteProductSignedError B Q N (fun q => (ρ q : ℂ)) (labelledProperPowerResidual k P W) := by
  rw [primeProductSignedError_eq_vonMangoldt_sub_properPower k P N Q B ρ W hB]
  congr 1
  unfold finiteProductSignedError
  simp_rw [labelledVonMangoldtProductMass_eq_sum_heathBrownOrders k P R W hR hW, sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro q _
  rw [sum_comm (s := B), mul_sum]

end

end ImbalancedChen.Part3
