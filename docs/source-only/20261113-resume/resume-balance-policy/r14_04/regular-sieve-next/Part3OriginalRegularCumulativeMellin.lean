import ImbalancedChen.Part3ActualUnitBandMellinProbe
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! A positive cumulative test on the whole unbounded real spectral line,
in the exact Mellin convention of the physical Macdonald pair.  The
integral of the testing weight is quadratic in the endpoint.  This lemma
only removes the spectral cutoff; it does not estimate a geometric trace. -/
noncomputable section
namespace ImbalancedChen.Part3.OriginalRegularCumulativeMellin20261113
open Set Filter MeasureTheory Complex
open ActualUnitBandMellinProbe20261112

def density (t T : ℝ) : ℝ := T*‖probeIntegral T ((t:ℂ)*I)‖^2

private theorem continuous_density (t : ℝ) : ContinuousOn (density t) (Ioi 0) := by
  let b := fun T : ℝ => (Real.pi^3/4)*Real.sinh (Real.pi*T)/
    (Real.cosh (Real.pi*T)+Real.cosh (Real.pi*t))^2
  have cb : Continuous b := by
    refine (continuous_const.mul (Real.continuous_sinh.comp (continuous_const.mul continuous_id))).div
      (((Real.continuous_cosh.comp (continuous_const.mul continuous_id)).add continuous_const).pow 2) ?_
    intro x
    exact pow_ne_zero _ (add_pos (Real.cosh_pos _) (Real.cosh_pos _)).ne'
  apply cb.continuousOn.congr
  intro T hT
  change T*‖probeIntegral T ((t:ℂ)*I)‖^2=b T
  rw [gamma_norm T t hT]
  dsimp only [b]
  field_simp [hT.ne',(add_pos (Real.cosh_pos (Real.pi*T)) (Real.cosh_pos (Real.pi*t))).ne'] <;> ring

private theorem integrable_density (t : ℝ) {a b : ℝ} (ha : 0<a) (hab : a≤b) :
    IntervalIntegrable (density t) volume a b :=
  ((continuous_density t).mono (show uIcc a b⊆Ioi 0 by
    rw [uIcc_of_le hab]; exact fun _ h => ha.trans_le h.1)).intervalIntegrable

/-- One majorant, with absolute constant chosen before any spectral cutoff,
works for positive and negative t, at every unbounded height. -/
theorem cumulative_majorant : ∃ C : ℝ,0<C ∧ ∀ {K t : ℝ}, 2≤|t| → |t|≤K →
    (Real.cosh (Real.pi*t))⁻¹ ≤ C*(∫ T in (1:ℝ)..K,density t T) := by
  obtain ⟨C,hC,oneBand⟩ := reciprocal_cosh_le
  refine ⟨C,hC,?_⟩
  intro K t t2 tK
  let a := |t|-1
  let b := |t|
  have a1 : 1≤a := by dsimp [a]; linarith
  have ab : a≤b := by dsimp [a,b]; linarith
  have step : b-a=1 := by dsimp [a,b]; ring
  have ib := integrable_density t (zero_lt_one.trans_le a1) ab
  have ik := integrable_density t zero_lt_one (a1.trans (ab.trans tK))
  have grow : (∫ T in a..b,density t T) ≤ ∫ T in (1:ℝ)..K,density t T :=
    intervalIntegral.integral_mono_interval a1 ab tK (by
      filter_upwards [ae_restrict_mem (μ:=volume) (measurableSet_Ioc : MeasurableSet (Ioc (1:ℝ) K))] with T hT
      exact mul_nonneg (zero_le_one.trans hT.1.le) (sq_nonneg _)) ik
  calc
    _ = ∫ _T in a..b,(Real.cosh (Real.pi*t))⁻¹ := by
      rw [intervalIntegral.integral_const,step,one_smul]
    _ ≤ ∫ T in a..b,C*density t T := by
      apply intervalIntegral.integral_mono_on ab intervalIntegrable_const (ib.const_mul C)
      intro T hT
      have dt : | |t|-T |≤1 := abs_le.mpr ⟨by dsimp [b] at hT; linarith [hT.2],
        by dsimp [a] at hT; linarith [hT.1]⟩
      simpa only [density,mul_assoc] using oneBand (a1.trans hT.1) dt
    _ = C*(∫ T in a..b,density t T) := intervalIntegral.integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left grow hC.le

/-- The exact price of integrating the Mellin height weight in the diagonal
term is (K²−1)/2.  In particular this step has no K^ε or log K loss. -/
theorem diagonal_price (K : ℝ) : (∫ T in (1:ℝ)..K,T)=(K^2-1)/2 := by
  rw [integral_id] <;> ring

end ImbalancedChen.Part3.OriginalRegularCumulativeMellin20261113
end
