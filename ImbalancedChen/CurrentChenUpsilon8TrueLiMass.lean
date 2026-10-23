import ImbalancedChen.CurrentChenUpsilon8CoprimeGateBudget
import ImbalancedChen.CurrentChenUpsilon9TrueLiMass

/-!
# Leading-one transport on the literal eighth li mass

The actual eighth product image has a<N^(2/3), so every moving li
argument N/a is at least N^(1/3). The already proved real-variable
leading-one bound is therefore uniform on that whole original image.
Its logarithmic gap is at least1/3, and the true phi(a)<=a inequality
bounds the same positive profile by its literal reciprocal-totient mass.
No density, prime-sum mean or Upsilon mean is supplied by the caller.
-/

namespace ImbalancedChen

noncomputable section

open Filter Topology
open scoped BigOperators
open Classical
open MathlibNt.SieveTheory.LiuWeight
open MathlibNt.SieveTheory.BombieriVinogradov (trueLogarithmicIntegral)

/-- The literal eighth product-image logarithmic reciprocal-totient mass.
Neither its support nor its coefficient depends on a sieve modulus. -/
def currentChenUpsilon8LogTotientMass (N : ℕ) : ℝ :=
  ∑ a ∈ currentChenUpsilon8PrefixProducts N,
    (1 / (Nat.totient a : ℝ)) *
      (1 / (1 - Real.log (a : ℝ) / Real.log (N : ℝ)))

theorem currentChenUpsilon8LogTotientMass_nonneg {N : ℕ} (hN : 2 ≤ N) :
    0 ≤ currentChenUpsilon8LogTotientMass N := by
  apply Finset.sum_nonneg
  intro a ha
  have hgap : 0 < 1 - Real.log (a : ℝ) / Real.log (N : ℝ) :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 3)
      (currentChenUpsilon8_log_gap_lower hN ha)
  exact mul_nonneg (one_div_nonneg.mpr (Nat.cast_nonneg _))
    (one_div_nonneg.mpr hgap.le)

/-- The genuine real leading-one bound is uniform on every actual eighth
product. All moving-argument and positive-denominator gates are paid here. -/
theorem eventually_currentChenUpsilon8_liMainMass_le_logTotientMass
    (η : ℝ) (hη : 0 < η) :
    ∀ᶠ N : ℕ in atTop,
      currentChenUpsilon8LiMainMass N ≤
        (1 + η) * ((N : ℝ) / Real.log (N : ℝ)) * currentChenUpsilon8LogTotientMass N := by
  obtain ⟨X, hX⟩ := eventually_atTop.mp (eventually_currentChenUpsilon9_trueLi_real_le η hη)
  have hlarge : ∀ᶠ N : ℕ in atTop, X ≤ (N : ℝ) ^ (1 / 3 : ℝ) :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 3)).comp
      tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop X)
  filter_upwards [hlarge, eventually_ge_atTop (2 : ℕ)] with N hlarge hN
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hNp : (0 : ℝ) < N := zero_lt_one.trans hNr
  have hlog := Real.log_pos hNr
  have hnormalized : currentChenUpsilon8LiMainMass N * Real.log (N : ℝ) / (N : ℝ) ≤
      (1 + η) * currentChenUpsilon8LogTotientMass N := by
    rw [currentChenUpsilon8LiMainMass, Finset.sum_mul, Finset.sum_div,
      currentChenUpsilon8LogTotientMass, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro a ha
    have hap : (0 : ℝ) < a := by
      exact_mod_cast (currentChenUpsilon8PrefixProducts_data ha).1
    have hgap : 0 < 1 - Real.log (a : ℝ) / Real.log (N : ℝ) :=
      lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 3)
        (currentChenUpsilon8_log_gap_lower hN ha)
    have hquot := currentChenUpsilon8_li_argument_power_lower hNr.le ha
    have hli := hX ((N : ℝ) / (a : ℝ)) (hlarge.trans hquot)
    have hφ : (0 : ℝ) < Nat.totient a := by
      exact_mod_cast Nat.totient_pos.mpr (currentChenUpsilon8PrefixProducts_data ha).1
    have hweight : 1 / (a : ℝ) ≤ 1 / (Nat.totient a : ℝ) :=
      one_div_le_one_div_of_le hφ (by exact_mod_cast Nat.totient_le a)
    have hlogquot : Real.log ((N : ℝ) / (a : ℝ)) =
        Real.log (N : ℝ) * (1 - Real.log (a : ℝ) / Real.log (N : ℝ)) := by
      rw [Real.log_div hNp.ne' hap.ne']
      field_simp [hlog.ne']
    calc
      _ ≤ ((1 + η) * ((N : ℝ) / (a : ℝ)) / Real.log ((N : ℝ) / (a : ℝ))) *
          (Real.log (N : ℝ) / (N : ℝ)) := by
        simpa only [trueLogarithmicIntegral, mul_div_assoc] using mul_le_mul_of_nonneg_right hli
          (div_nonneg hlog.le hNp.le)
      _ = (1 + η) * ((1 / (a : ℝ)) *
          (1 / (1 - Real.log (a : ℝ) / Real.log (N : ℝ)))) := by
        rw [hlogquot]
        field_simp [hNp.ne', hap.ne', hlog.ne', hgap.ne']
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hweight (one_div_nonneg.mpr hgap.le)) (by linarith only [hη])
  calc
    _ ≤ ((1 + η) * currentChenUpsilon8LogTotientMass N * (N : ℝ)) / Real.log (N : ℝ) :=
      (le_div_iff₀ hlog).mpr ((div_le_iff₀ hNp).mp hnormalized)
    _ = _ := by ring

end

end ImbalancedChen
