import ImbalancedChen.Part3PhysicalSmoothReciprocalPoisson
import Mathlib.Data.Nat.Totient

/-!
Source-only, uncompiled strengthening of the triangle bound for the actual
`OriginalSmoothPoissonTail.kloosterman` definition. This is a new theorem in
a separate module; it does not change the original theorem.
-/

noncomputable section
attribute [local instance] Classical.propDecidable

namespace ImbalancedChen.Part3.OriginalSmoothPoissonTail
open Classical
open scoped BigOperators SchwartzMap FourierTransform

/-- The triangle bound counts exactly the coprime residue terms, including
the empty range for `c = 0` and the single coprime residue for `c = 1`. -/
theorem kloosterman_norm_le_totient (c : ℕ) (m n : ℤ) :
    ‖kloosterman c m n‖ ≤ (Nat.totient c : ℝ) := by
  unfold kloosterman
  calc
    _ ≤ ∑ u ∈ Finset.range c,
        ‖if Nat.Coprime u c then
          fourier 1 (((m * (u : ℤ) + n * inverseResidue c u : ℤ) : ℝ) /
            (c : ℝ) : UnitAddCircle) else 0‖ := norm_sum_le _ _
    _ ≤ ∑ u ∈ Finset.range c,
        if Nat.Coprime u c then (1 : ℝ) else 0 := by
      apply Finset.sum_le_sum
      intro u hu
      split_ifs <;> simp only [fourier_apply, Circle.norm_coe,
        norm_zero, le_refl]
    _ = (((Finset.range c).filter (fun u => Nat.Coprime u c)).card : ℝ) := by
      simp
    _ = (Nat.totient c : ℝ) := by
      congr 1
      simp only [Nat.totient_eq_card_coprime, Nat.coprime_comm]

end ImbalancedChen.Part3.OriginalSmoothPoissonTail
