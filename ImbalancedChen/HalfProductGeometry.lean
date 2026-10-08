import ImbalancedChen.OrderedBad
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Convert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Elementary geometry of the discarded half-products

The strict curved-boundary condition `q ^ b < r`, together with a positive
lower cutoff `T ≤ r * q`, forces `T ^ (b / (1 + b)) < r`. When `r ≤ q`,
the same strict bound holds for both factors. The argument works for every
positive real `b`; the manuscript's additional restriction `b < 1` is not
needed for this geometric implication.

The localization theorem applies this geometry to the actual finite predicate
`BadReceiver`. The final theorem evaluates the elementary integral that gives
the displayed coefficient `log (1 / b)`. No prime-counting asymptotic, sieve
estimate, or distribution hypothesis is assumed or proved in this file.
-/

namespace ImbalancedChen

/-- A product above the lower cutoff and below the curved bad boundary has
a strictly large first factor. Positivity, rather than primality, suffices. -/
theorem halfProduct_rpow_lt_left {b T r q : ℝ}
    (hb : 0 < b) (hT : 0 < T) (hr : 0 < r) (hq : 0 < q)
    (hbad : q ^ b < r) (hcut : T ≤ r * q) :
    T ^ (b / (1 + b)) < r := by
  have hden : 0 < 1 + b := by linarith
  have hlogBad : b * Real.log q < Real.log r := by
    have h := (Real.log_lt_log_iff (Real.rpow_pos_of_pos hq b) hr).2 hbad
    simpa only [Real.log_rpow hq b] using h
  have hlogCut : Real.log T ≤ Real.log r + Real.log q := by
    have h := Real.log_le_log hT hcut
    simpa only [Real.log_mul (ne_of_gt hr) (ne_of_gt hq)] using h
  apply (Real.log_lt_log_iff
    (Real.rpow_pos_of_pos hT (b / (1 + b))) hr).1
  rw [Real.log_rpow hT (b / (1 + b)), div_mul_eq_mul_div]
  apply (div_lt_iff₀ hden).2
  nlinarith [mul_le_mul_of_nonneg_left hlogCut (le_of_lt hb)]

/-- The manuscript's ordered half-product region has two strictly rough
factors. This includes the square case `r = q`. -/
theorem halfProduct_rpow_lt_factors {b T r q : ℝ}
    (hb : 0 < b) (hT : 0 < T) (hr : 0 < r) (hq : 0 < q)
    (hbad : q ^ b < r) (hrq : r ≤ q) (hcut : T ≤ r * q) :
    T ^ (b / (1 + b)) < r ∧ T ^ (b / (1 + b)) < q := by
  have h := halfProduct_rpow_lt_left hb hT hr hq hbad hcut
  exact ⟨h, lt_of_lt_of_le h hrq⟩

/-- The non-strict roughness bound as displayed in the manuscript. -/
theorem halfProduct_rpow_le_factors {b T r q : ℝ}
    (hb : 0 < b) (hT : 0 < T) (hr : 0 < r) (hq : 0 < q)
    (hbad : q ^ b < r) (hrq : r ≤ q) (hcut : T ≤ r * q) :
    T ^ (b / (1 + b)) ≤ r ∧ T ^ (b / (1 + b)) ≤ q := by
  obtain ⟨hleft, hright⟩ := halfProduct_rpow_lt_factors hb hT hr hq hbad hrq hcut
  exact ⟨le_of_lt hleft, le_of_lt hright⟩

/-- Prime factors satisfy the real geometric bound without changing the
strictness of the manuscript's bad-region inequality. -/
theorem prime_halfProduct_rpow_lt_factors {b T : ℝ} {r q : ℕ}
    (hb : 0 < b) (hT : 0 < T) (hr : Nat.Prime r) (hq : Nat.Prime q)
    (hbad : (q : ℝ) ^ b < (r : ℝ)) (hrq : r ≤ q)
    (hcut : T ≤ (r * q : ℕ)) :
    T ^ (b / (1 + b)) < (r : ℝ) ∧ T ^ (b / (1 + b)) < (q : ℝ) := by
  have hrR : (0 : ℝ) < (r : ℝ) := Nat.cast_pos.mpr hr.pos
  have hqR : (0 : ℝ) < (q : ℝ) := Nat.cast_pos.mpr hq.pos
  have hrqR : (r : ℝ) ≤ (q : ℝ) := Nat.cast_le.mpr hrq
  have hcutR : T ≤ (r : ℝ) * (q : ℝ) := by
    simpa only [Nat.cast_mul] using hcut
  exact halfProduct_rpow_lt_factors hb hT hrR hqR hbad hrqR hcutR

/-- Every actual bad receiver above a positive cutoff has ordered prime
factors in the curved bad region, and both factors exceed the roughness
threshold. The exponent is left in its literal `b / (1 + b)` form for
`b = num / den`. -/
theorem badReceiver_exists_rough_factors {num den m : ℕ} {T : ℝ}
    (hnum : 0 < num) (hden : 0 < den) (hT : 0 < T)
    (hbad : BadReceiver num den m) (hcut : T ≤ (m : ℝ)) :
    ∃ r q : ℕ, Nat.Prime r ∧ Nat.Prime q ∧ m = r * q ∧ r ≤ q ∧
      (q : ℝ) ^ ((num : ℝ) / (den : ℝ)) < (r : ℝ) ∧
      T ^ (((num : ℝ) / (den : ℝ)) / (1 + (num : ℝ) / (den : ℝ))) < (r : ℝ) ∧
      T ^ (((num : ℝ) / (den : ℝ)) / (1 + (num : ℝ) / (den : ℝ))) < (q : ℝ) := by
  obtain ⟨r, q, hr, hq, hm, hrq, hpow⟩ :=
    (badReceiver_iff_ordered_real_factors hden).1 hbad
  have hnumR : (0 : ℝ) < (num : ℝ) := Nat.cast_pos.mpr hnum
  have hdenR : (0 : ℝ) < (den : ℝ) := Nat.cast_pos.mpr hden
  have hcut' : T ≤ (r * q : ℕ) := by simpa only [hm] using hcut
  obtain ⟨hleft, hright⟩ :=
    prime_halfProduct_rpow_lt_factors (div_pos hnumR hdenR) hT hr hq hpow hrq hcut'
  exact ⟨r, q, hr, hq, hm, hrq, hpow, hleft, hright⟩

/-- The fixed integration interval from the half-product calculation lies
strictly inside `(0, 1)` when `0 < b < 1`. -/
theorem halfProduct_exponent_pos_lt_half {b : ℝ} (hb : 0 < b) (hb1 : b < 1) :
    0 < b / (1 + b) ∧ b / (1 + b) < 1 / 2 := by
  have hden : 0 < 1 + b := by linarith
  refine ⟨div_pos hb hden, (div_lt_iff₀ hden).2 ?_⟩
  linarith

/-- Exact elementary evaluation of the manuscript's half-product integral.
This identifies its coefficient; it does not prove that this integral is an
asymptotic for the number of prime half-products. -/
theorem halfProduct_integral {b : ℝ} (hb : 0 < b) (hb1 : b < 1) :
    (∫ u in (b / (1 + b))..(1 / 2 : ℝ), 1 / (u * (1 - u))) =
      Real.log (1 / b) := by
  let a : ℝ := b / (1 + b)
  have ha : 0 < a := (halfProduct_exponent_pos_lt_half hb hb1).1
  have hab : a ≤ 1 / 2 := (halfProduct_exponent_pos_lt_half hb hb1).2.le
  have ha1 : a < 1 := by linarith
  have hmem : ∀ x ∈ Set.uIcc a (1 / 2 : ℝ), 0 < x ∧ x < 1 := by
    intro x hx
    rw [Set.uIcc_of_le hab] at hx
    exact ⟨lt_of_lt_of_le ha hx.1, by linarith [hx.2]⟩
  have hderiv : ∀ x ∈ Set.uIcc a (1 / 2 : ℝ),
      HasDerivAt (fun u : ℝ => Real.log u - Real.log (1 - u))
        (1 / (x * (1 - x))) x := by
    intro x hx
    have hx0 : x ≠ 0 := ne_of_gt (hmem x hx).1
    have hx1 : 1 - x ≠ 0 := ne_of_gt (sub_pos.mpr (hmem x hx).2)
    have h := (Real.hasDerivAt_log hx0).sub
      (((hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x)).log hx1)
    convert h using 1 <;> field_simp [hx0, hx1] <;> ring
  have hint : IntervalIntegrable (fun u : ℝ => 1 / (u * (1 - u)))
      MeasureTheory.volume a (1 / 2 : ℝ) := by
    apply ContinuousOn.intervalIntegrable
    refine continuousOn_const.div
      (continuousOn_id.mul (continuousOn_const.sub continuousOn_id)) ?_
    intro x hx
    exact mul_ne_zero (ne_of_gt (hmem x hx).1)
      (ne_of_gt (sub_pos.mpr (hmem x hx).2))
  have hden : 0 < 1 + b := by linarith
  have hratio : (1 - a) / a = 1 / b := by
    dsimp only [a]
    field_simp [ne_of_gt hb, ne_of_gt hden] <;> ring
  have hhalf : (1 : ℝ) - 1 / 2 = 1 / 2 := by norm_num
  calc
    (∫ u in (b / (1 + b))..(1 / 2 : ℝ), 1 / (u * (1 - u))) =
        (Real.log (1 / 2) - Real.log (1 - 1 / 2)) -
          (Real.log a - Real.log (1 - a)) :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
    _ = Real.log (1 - a) - Real.log a := by rw [hhalf]; ring
    _ = Real.log ((1 - a) / a) :=
      (Real.log_div (ne_of_gt (sub_pos.mpr ha1)) (ne_of_gt ha)).symm
    _ = Real.log (1 / b) := by rw [hratio]

end ImbalancedChen
