import ImbalancedChen.P2OriginalSaving19HigherMoments
import ImbalancedChen.P2OriginalSaving19PrefixMoments

/-!
SOURCE CANDIDATE, NOT COMPILED. Specialize the existing verified Winner9
prefix evaluator to the unchanged Saving19 authorMoment/rationalMoment.
The only normalization premises are exact integer-coordinate encodings.
No saved Q80/Q96 floor or geometry/ownership conclusion is a premise.
This is finite representation work, not a new manuscript-external estimate.
-/
namespace ImbalancedChen.P2OriginalSaving19HigherMomentsPrefix

open scoped BigOperators
open P2OriginalSaving19HigherMoments
open P2OriginalSaving19PrefixMoments

/-- The table uses the original completeH equations; no coefficient identity
is supplied as an extra assumption to this Saving19 specialization. -/
theorem normalizedMoment_eq_author (g z : Fin 9 → Nat) (d k : Nat) (hk : k ≤ 6) :
    normalizedMoment g z d k =
      authorMoment (fun i => (g i : ℚ)) (fun i => (z i : ℚ)) k / (d : ℚ) ^ k := by
  rw [normalizedMoment_eq_convolution completeH (fun _ => rfl)
    (fun _ _ _ => rfl) g z d k hk]
  simp only [authorMoment, div_mul_eq_div_div]

/-- Exact common-denominator form of the original rational moment, through
all degrees needed by the manuscript's degree-six log correction. -/
theorem normalizedMoment_eq_rationalMoment (g z : Fin 9 → Nat) (d k : Nat)
    (hd : d ≠ 0) (hk : k ≤ 6) :
    normalizedMoment g z d k =
      rationalMoment (fun i => (g i : ℚ)) (fun i => (z i : ℚ) / (d : ℚ)) k := by
  rw [normalizedMoment_eq_author g z d k hk,
    authorMoment_eq_rationalMoment _ _ k hk,
    rationalMoment_common_denominator _ _ (d : ℚ) (by exact_mod_cast hd) k]
  simp only [rationalMoment, div_mul_eq_div_div]

/-- The original rational arrays are related to nonnegative integer arrays by
closed per-coordinate identities. A common positive gap scale cancels. -/
theorem normalizedMoment_eq_encoded (g z : Fin 9 → Nat) (d s k : Nat)
    (hd : d ≠ 0) (hs : s ≠ 0) (hk : k ≤ 6)
    (gaps deviations : Fin 9 → ℚ)
    (hg : ∀ i, gaps i = (g i : ℚ) / (s : ℚ))
    (hz : ∀ i, deviations i = (z i : ℚ) / (d : ℚ)) :
    normalizedMoment g z d k = rationalMoment gaps deviations k := by
  have hga : gaps = fun i => (s : ℚ)⁻¹ * (g i : ℚ) := by
    funext i
    rw [hg i, div_eq_mul_inv, mul_comm]
  have hza : deviations = fun i => (z i : ℚ) / (d : ℚ) := funext hz
  rw [hga, hza,
    rationalMoment_gap_scale _ _ (s : ℚ)⁻¹
      (inv_ne_zero (by exact_mod_cast hs)) k]
  exact normalizedMoment_eq_rationalMoment g z d k hd hk

#print axioms normalizedMoment_eq_author
#print axioms normalizedMoment_eq_rationalMoment
#print axioms normalizedMoment_eq_encoded

end ImbalancedChen.P2OriginalSaving19HigherMomentsPrefix
