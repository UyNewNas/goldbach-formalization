import ImbalancedChen.Part3OriginalCommonPoissonLanesCore
import Mathlib.Tactic

namespace ImbalancedChen.Part3.OriginalClassicalSpectralSupports20261102

noncomputable section
open Classical Finset
open OriginalCommonPoissonLanes20261102

/-- This scale is only for the classical support theorem.  The normalized
physical amplitude and common phase still use V=2^j. -/
def classicalMScale (j : ℕ) : ℝ := ((2 : ℕ)^j : ℝ) - 1/2

theorem classicalMScale_bounds (j : ℕ) :
    (1 : ℝ)/2 ≤ classicalMScale j ∧
      ((2 : ℕ)^j : ℝ)/2 ≤ classicalMScale j ∧
      classicalMScale j ≤ ((2 : ℕ)^j : ℝ) := by
  have hvN : 1 ≤ (2 : ℕ)^j := pow_pos (by norm_num : (0 : ℕ) < 2) j
  have hv : (1 : ℝ) ≤ ((2 : ℕ)^j : ℝ) := by exact_mod_cast hvN
  unfold classicalMScale
  norm_num only [Nat.cast_pow, Nat.cast_ofNat] at hv ⊢
  constructor
  · linarith only [hv]
  constructor <;> linarith only [hv]

/-- The entire original clipped interval, including its left endpoint,
belongs to the same printed dyadic interval at every level. -/
theorem commonMBlock_classical_support (J j : ℕ) {m : ℕ}
    (hm : m ∈ commonMBlock J j) :
    classicalMScale j < (m : ℝ) ∧
      (m : ℝ) ≤ 2*classicalMScale j := by
  obtain ⟨hlo, hhi⟩ := mem_Ico.mp hm
  have hupper : m < 2*(2 : ℕ)^j := by
    simpa only [pow_succ, Nat.mul_comm] using (lt_min_iff.mp hhi).1
  have hupper' : m+1 ≤ 2*(2 : ℕ)^j := by omega
  have hloR : ((2 : ℕ)^j : ℝ) ≤ (m : ℝ) := by exact_mod_cast hlo
  have hhiR : (m : ℝ)+1 ≤ 2*((2 : ℕ)^j : ℝ) := by exact_mod_cast hupper'
  unfold classicalMScale
  norm_num only [Nat.cast_pow, Nat.cast_ofNat] at hloR hhiR ⊢
  constructor
  · linarith only [hloR]
  · linarith only [hhiR]

/-- The same frozen interval/phase object is retained at the changed
classical support scale: no level-dependent mask or phase is introduced. -/
theorem commonPoissonCompleted_classical_support (J j : ℕ) (k1 : ℤ) {m : ℕ}
    (hm : m ∈ commonMBlock J j) :
    (1 : ℝ)/2 ≤ classicalMScale j ∧
      (m : ℝ) ∈ Set.Ioc (classicalMScale j) (2*classicalMScale j) ∧
      (commonPoissonCompleted J j k1).weight m =
        Complex.exp (2*(Real.pi : ℂ)*Complex.I*
          ((k1 : ℝ)/(64*(2^j : ℕ)) : ℝ)*(m : ℂ)) := by
  exact ⟨(classicalMScale_bounds j).1, commonMBlock_classical_support J j hm,
    commonPoissonCompleted_weight J j k1 m hm⟩

end
end ImbalancedChen.Part3.OriginalClassicalSpectralSupports20261102
