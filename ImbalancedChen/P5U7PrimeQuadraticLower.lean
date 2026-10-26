import ImbalancedChen.P5U7PrimeInteriorExtinctionLower

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Matching explicit quadratic lower extinction from an actual shrinking
positive interior interval. This completes the concrete extinction-family
primitive: no lower-integral or rate premise, and no arithmetic squeeze.
-/
namespace ImbalancedChen
noncomputable section
open Set MeasureTheory Filter Topology
open Classical

def p5U7PrimeQuadraticLowerConstant : ℝ := (59/250 : ℝ)^4/4

theorem p5U7PrimeQuadraticLowerConstant_pos : 0 < p5U7PrimeQuadraticLowerConstant := by
  unfold p5U7PrimeQuadraticLowerConstant
  positivity

/-- The actual positive-part integral dominates the constant positive
amplitude on a genuine shrinking interior subinterval. -/
theorem p5U7PrimeLeadingIntegral_quadratic_lower (eta : ℝ)
    (hetaL : (73/59 : ℝ)-1 ≤ eta) (hetaH : eta ≤ (73/59 : ℝ)) :
    p5U7PrimeQuadraticLowerConstant*((73/59 : ℝ)-eta)^2 ≤
      p5U7PrimeLeadingIntegral eta := by
  have heta : 0 ≤ eta := by linarith only [hetaL]
  let f : ℝ → ℝ := fun t => max 0 (p5U7PrimeCutoffLogRow eta t)
  let D : ℝ := ((59/250 : ℝ)^2/2)*((73/59 : ℝ)-eta)
  have hi := p5U7PrimeExtinction_interior_interval heta hetaH
  have hsubU : p5U7PrimeExtinctionInteriorEnd eta ≤ (1/3 : ℝ) := hi.2.1.trans hi.2.2
  have hcont : ContinuousOn f (Icc (59/250 : ℝ) (1/3)) :=
    continuousOn_const.max (p5U7PrimeCutoffLogRow_continuousOn eta heta)
  have hIfull : IntervalIntegrable f volume (59/250 : ℝ) (1/3) :=
    p5U7PrimeCutoffLogPositive_intervalIntegrable eta heta
  have hIsub : IntervalIntegrable f volume (59/250 : ℝ) (p5U7PrimeExtinctionInteriorEnd eta) :=
    ContinuousOn.intervalIntegrable_of_Icc hi.1
      (hcont.mono (fun t ht => ⟨ht.1,ht.2.trans hsubU⟩))
  have hpoint : ∀ t ∈ Icc (59/250 : ℝ) (p5U7PrimeExtinctionInteriorEnd eta), D ≤ f t := by
    intro t ht
    exact (p5U7PrimeExtinction_interior_log_lower hetaL hetaH ht).trans (le_max_right _ _)
  have hsmall := intervalIntegral.integral_mono_on hi.1
    (continuous_const.intervalIntegrable (59/250) (p5U7PrimeExtinctionInteriorEnd eta)) hIsub hpoint
  have hbig : (∫ t in (59/250 : ℝ)..(p5U7PrimeExtinctionInteriorEnd eta), f t) ≤
      ∫ t in (59/250 : ℝ)..(1/3 : ℝ), f t :=
    intervalIntegral.integral_mono_interval (le_refl (59/250 : ℝ)) hi.1 hsubU
      (Eventually.of_forall (fun t => le_max_left 0 (p5U7PrimeCutoffLogRow eta t))) hIfull
  have hconstant : (∫ t in (59/250 : ℝ)..(p5U7PrimeExtinctionInteriorEnd eta), D) =
      p5U7PrimeQuadraticLowerConstant*((73/59 : ℝ)-eta)^2 := by
    rw [intervalIntegral.integral_const]
    simp only [smul_eq_mul,p5U7PrimeExtinctionInteriorEnd,p5U7PrimeQuadraticLowerConstant,D]
    ring
  rw [hconstant] at hsmall
  have hnative : p5U7PrimeLeadingIntegral eta =
      ∫ t in (59/250 : ℝ)..(1/3 : ℝ), f t :=
    p5U7PrimeLeadingIntegral_eq_log_positive_part eta heta
  rw [← hnative] at hbig
  exact hsmall.trans hbig

/-- Genuine matching quadratic order with explicit positive lower and
upper constants on the fixed left neighborhood H-1<=eta<=H. -/
theorem p5U7PrimeLeadingIntegral_quadratic_sandwich (eta : ℝ)
    (hetaL : (73/59 : ℝ)-1 ≤ eta) (hetaH : eta ≤ (73/59 : ℝ)) :
    p5U7PrimeQuadraticLowerConstant*((73/59 : ℝ)-eta)^2 ≤ p5U7PrimeLeadingIntegral eta ∧
      p5U7PrimeLeadingIntegral eta ≤ (1/2 : ℝ)*((73/59 : ℝ)-eta)^2 := by
  have heta : 0 ≤ eta := by linarith only [hetaL]
  exact ⟨p5U7PrimeLeadingIntegral_quadratic_lower eta hetaL hetaH,
    (p5U7PrimeLeadingIntegral_quadratic_extinction eta heta hetaH).2⟩
end
end ImbalancedChen
