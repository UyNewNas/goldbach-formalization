import ImbalancedChen.ActualThirdOriginalP4ABalancedSymmetricLeaf
import ImbalancedChen.ActualThirdOriginalP4AOrdinaryFiniteSelector

/- SOURCEONLY / UNCOMPILED. Exact bridge from the producer's min BEFORE
mass multiplication/UP to the min of the already mass-scaled integer costs
used by the symmetric finite dispatcher. No fallback estimate is assumed. -/
namespace ImbalancedChen.P0SymmetricOuterMinBridge
noncomputable section
open OriginalThirdClippedChordSourceOnly OriginalThirdRoundedNewSourceOnly
open OriginalThirdSymmetricMassCeilSourceOnly
open OriginalThirdP4ASymmetricTentPrerequisites OriginalThirdP4ABalancedSymmetricLeaf
open OriginalThirdSymmetricJensenSourceOnly
open OriginalThirdP4AOrdinaryFiniteSelectorSourceOnly

theorem up_mono {a b d : ℤ} (hd : 0 < d) (hab : a ≤ b) : up a d ≤ up b d := by
  unfold up
  exact neg_le_neg (Int.ediv_le_ediv hd (neg_le_neg hab))

theorem literal_upper_mono (x0 x1 z0 z1 : ℤ)
    (hmass : 0 ≤ (literalSymmetricMass x0 x1 z0 z1).hi) :
    Monotone (literalSymmetricUpper x0 x1 z0 z1) := by
  intro a b hab
  unfold literalSymmetricUpper
  exact up_mono P160_pos (mul_le_mul_of_nonneg_right hab hmass)

/-- Increasing integer ceiling preserves a finite minimum exactly. No
rounding reserve is consumed, and high or mean may be signed integers. -/
theorem literal_upper_min (x0 x1 z0 z1 fallback mean : ℤ)
    (hmass : 0 ≤ (literalSymmetricMass x0 x1 z0 z1).hi) :
    literalSymmetricUpper x0 x1 z0 z1 (min fallback mean) =
      min (literalSymmetricUpper x0 x1 z0 z1 fallback)
        (literalSymmetricUpper x0 x1 z0 z1 mean) := by
  rcases le_total fallback mean with h | h
  · rw [min_eq_left h, min_eq_left (literal_upper_mono x0 x1 z0 z1 hmass h)]
  · rw [min_eq_right h, min_eq_right (literal_upper_mono x0 x1 z0 z1 hmass h)]

/-- This is the actual original raw Option-mean helper, transported through
the exact symmetric mass and final integer UP. None keeps the fallback. -/
theorem literal_upper_optional_mean (x0 x1 z0 z1 fallback : ℤ) (mean : Option ℤ)
    (hmass : 0 ≤ (literalSymmetricMass x0 x1 z0 z1).hi) :
    literalSymmetricUpper x0 x1 z0 z1 (applyOptionalMean fallback mean) =
      match mean with
      | none => literalSymmetricUpper x0 x1 z0 z1 fallback
      | some j => min (literalSymmetricUpper x0 x1 z0 z1 fallback)
          (literalSymmetricUpper x0 x1 z0 z1 j) := by
  cases mean with
  | none => rfl
  | some j => exact literal_upper_min x0 x1 z0 z1 fallback j hmass

/-- The actual half-mass enclosure supplies the needed nonnegative integer
mass internally from the original positive symmetric full-cell geometry. -/
theorem literal_mass_hi_nonneg (x0 x1 z0 z1 : ℤ) (a b c d : ℚ)
    (ha : a=(x0:ℚ)/((48000*2^24:ℤ):ℚ))
    (hb : b=(x1:ℚ)/((48000*2^24:ℤ):ℚ))
    (hc : c=(z0:ℚ)/((48000*2^24:ℤ):ℚ))
    (hd : d=(z1:ℚ)/((48000*2^24:ℤ):ℚ))
    (hg : SymmetricFullBox (a:ℝ) (b:ℝ) (c:ℝ) (d:ℝ))
    (hratio : (b:ℝ)/(a:ℝ) ≤ 2) :
    0 ≤ (literalSymmetricMass x0 x1 z0 z1).hi := by
  have hmass := (literal_symmetric_mass_encloses_ratio x0 x1 z0 z1 a b c d
    ha hb hc hd hg hratio).2
  have hnonneg := (symmetric_prism_mass_pos hg).le.trans hmass
  exact value_le_iff.mp (by simpa only [value_zero] using hnonneg)

end
end ImbalancedChen.P0SymmetricOuterMinBridge
