import ImbalancedChen.Part3DistributionTargets
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Tactic

/-!
SOURCEONLY, 2026-10-24. UNCOMPILED; no acceptance credit.
The finite geometric identity and elementary bounds for the actual common
completed interval and additive phase in Part3DistributionTargets.
No averaged logarithmic L1 estimate is asserted here.
-/

namespace ImbalancedChen.Part3.ActualIntervalGeometricSumSourceOnly
noncomputable section
open scoped BigOperators

/-- The single-step exponential of the actual additive phase. -/
def phaseBase (α : ℝ) : ℂ :=
  Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (α : ℂ))

/-- Exactly the exponential occurring inside CommonCompletedVariable.weight. -/
def phaseAt (α : ℝ) (m : ℕ) : ℂ :=
  Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (α : ℂ) * (m : ℂ))

private lemma phaseAt_eq_pow (α : ℝ) (m : ℕ) :
    phaseAt α m = phaseBase α ^ m := by
  calc
    phaseAt α m =
        Complex.exp ((m : ℂ) *
          (2 * (Real.pi : ℂ) * Complex.I * (α : ℂ))) := by
      unfold phaseAt
      congr 1
      ring
    _ = phaseBase α ^ m := by
      rw [Complex.exp_nat_mul]
      rfl

private lemma phaseBase_norm (α : ℝ) : ‖phaseBase α‖ = 1 := by
  have he : phaseBase α =
      Complex.exp (((2 * Real.pi * α : ℝ) : ℂ) * Complex.I) := by
    unfold phaseBase
    congr 1
    push_cast
    ring
  rw [he, Complex.norm_exp_ofReal_mul_I]

private lemma phaseAt_norm (α : ℝ) (m : ℕ) : ‖phaseAt α m‖ = 1 := by
  rw [phaseAt_eq_pow, norm_pow, phaseBase_norm, one_pow]

/-- The phase geometric sum, valid also for an empty interval. -/
theorem phase_geom_identity (α : ℝ) {lo hi : ℕ} (hlo : lo ≤ hi) :
    (1 - phaseBase α) *
        (∑ m ∈ Finset.Ico lo hi, phaseAt α m) =
      phaseAt α lo - phaseAt α hi := by
  simp_rw [phaseAt_eq_pow]
  rw [mul_comm (1 - phaseBase α)
    (∑ m ∈ Finset.Ico lo hi, phaseBase α ^ m)]
  exact geom_sum_Ico_mul_neg (phaseBase α) hlo

private lemma phase_sum_length_bound (α : ℝ) {lo hi : ℕ} (hlo : lo ≤ hi) :
    ‖∑ m ∈ Finset.Ico lo hi, phaseAt α m‖ ≤
      ((hi - lo : ℕ) : ℝ) := by
  calc
    ‖∑ m ∈ Finset.Ico lo hi, phaseAt α m‖ ≤
        ∑ m ∈ Finset.Ico lo hi, ‖phaseAt α m‖ := norm_sum_le _ _
    _ = ((hi - lo : ℕ) : ℝ) := by
      simp [phaseAt_norm, Nat.card_Ico]

private lemma phase_sum_denominator_bound (α : ℝ) {lo hi : ℕ}
    (hlo : lo ≤ hi) (hne : phaseBase α ≠ 1) :
    ‖∑ m ∈ Finset.Ico lo hi, phaseAt α m‖ ≤
      2 / ‖1 - phaseBase α‖ := by
  have hden : 0 < ‖1 - phaseBase α‖ := by
    apply norm_pos_iff.mpr
    exact sub_ne_zero.mpr (Ne.symm hne)
  have hends : ‖phaseAt α lo - phaseAt α hi‖ ≤ (2 : ℝ) := by
    calc
      ‖phaseAt α lo - phaseAt α hi‖ ≤
          ‖phaseAt α lo‖ + ‖phaseAt α hi‖ := norm_sub_le _ _
      _ = 2 := by simp [phaseAt_norm]
  have hmul :
      ‖1 - phaseBase α‖ *
          ‖∑ m ∈ Finset.Ico lo hi, phaseAt α m‖ ≤ 2 := by
    calc
      ‖1 - phaseBase α‖ *
          ‖∑ m ∈ Finset.Ico lo hi, phaseAt α m‖ =
          ‖(1 - phaseBase α) *
            (∑ m ∈ Finset.Ico lo hi, phaseAt α m)‖ :=
        (norm_mul _ _).symm
      _ = ‖phaseAt α lo - phaseAt α hi‖ := by
        rw [phase_geom_identity α hlo]
      _ ≤ 2 := hends
  exact (le_div_iff₀ hden).2 (by simpa [mul_comm] using hmul)

/-- The requested min bound for every real additive phase off resonance. -/
theorem phase_sum_norm_le_min (α : ℝ) {lo hi : ℕ}
    (hlo : lo ≤ hi) (hne : phaseBase α ≠ 1) :
    ‖∑ m ∈ Finset.Ico lo hi, phaseAt α m‖ ≤
      min (((hi - lo : ℕ) : ℝ)) (2 / ‖1 - phaseBase α‖) := by
  exact le_min (phase_sum_length_bound α hlo)
    (phase_sum_denominator_bound α hlo hne)

private lemma completed_weight_sum (d : CommonCompletedVariable) :
    (∑ m ∈ Finset.Ico d.intervalLo d.intervalHi, d.weight m) =
      ∑ m ∈ Finset.Ico d.intervalLo d.intervalHi,
        phaseAt d.additivePhase m := by
  apply Finset.sum_congr rfl
  intro m hm
  simp [CommonCompletedVariable.weight, phaseAt, hm]

/-- The geometric identity specializes to the one common completed variable. -/
theorem completed_weight_geom_identity (d : CommonCompletedVariable)
    (hlo : d.intervalLo ≤ d.intervalHi) :
    (1 - phaseBase d.additivePhase) *
        (∑ m ∈ Finset.Ico d.intervalLo d.intervalHi, d.weight m) =
      phaseAt d.additivePhase d.intervalLo -
        phaseAt d.additivePhase d.intervalHi := by
  rw [completed_weight_sum d]
  exact phase_geom_identity d.additivePhase hlo

/-- A pointwise interval coefficient bound for the actual weight. -/
theorem completed_weight_sum_norm_le_min (d : CommonCompletedVariable)
    (hlo : d.intervalLo ≤ d.intervalHi)
    (hne : phaseBase d.additivePhase ≠ 1) :
    ‖∑ m ∈ Finset.Ico d.intervalLo d.intervalHi, d.weight m‖ ≤
      min (((d.intervalHi - d.intervalLo : ℕ) : ℝ))
        (2 / ‖1 - phaseBase d.additivePhase‖) := by
  rw [completed_weight_sum d]
  exact phase_sum_norm_le_min d.additivePhase hlo hne

end
end ImbalancedChen.Part3.ActualIntervalGeometricSumSourceOnly
