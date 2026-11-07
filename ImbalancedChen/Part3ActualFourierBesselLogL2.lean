import ImbalancedChen.Part3ActualFourierBesselConjugation
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED, 2026-10-26.
Exact cusp radial energy transport. For h(q)=(q/a)^(-1/2)c(q/a),
the logarithmic tail energy of h(exp r) equals the actual dy/y^2 energy
of c, with lower endpoint log(aY). The Jacobian is proved; there is no
remaining factor a. This consumes a raw height energy, not a premise
about the transformed mode. Extracting that raw energy from a cylinder
L2 test is already supplied by ActualCylinderFourierCoefficients.
-/

namespace ImbalancedChen.Part3.ActualFourierBesselLogL220261026a
noncomputable section
open Set MeasureTheory
open ActualMaassFourierODE20261026a ActualFourierBesselConjugation20261026a
attribute [local instance] Measure.Subtype.measureSpace

local instance periodCell_finite : IsFiniteMeasure (volume : Measure PeriodCell) := by
  constructor
  rw [Measure.Subtype.volume_univ measurableSet_Icc.nullMeasurableSet]
  exact isCompact_Icc.measure_lt_top

def heightEnergy (c : ℝ → ℂ) (y : ℝ) : ℝ := y⁻¹^2 * ‖c y‖^2
def logarithmicMode (c : ℝ → ℂ) (a r : ℝ) : ℂ := besselTransform c a (Real.exp r)

theorem normalizedHeight_norm_sq (c : ℝ → ℂ) {y : ℝ} (hy : 0 < y) :
    ‖normalizedHeight c y‖^2 = y⁻¹ * ‖c y‖^2 := by
  have hp : (y ^ (-1/2 : ℝ))^2 = y⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hy.le]
    norm_num
  simp only [normalizedHeight, heightPower, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hy.le _), mul_pow, hp]

theorem scaledExp_image_Ioi {a : ℝ} (ha : 0 < a) (R : ℝ) :
    (fun r : ℝ => Real.exp r/a) '' Ioi R = Ioi (Real.exp R/a) := by
  ext y
  constructor
  · rintro ⟨r, hr, rfl⟩
    exact (div_lt_div_iff_of_pos_right ha).mpr (Real.exp_lt_exp.mpr hr)
  · intro hy
    have hpos : 0 < y := (div_pos (Real.exp_pos R) ha).trans hy
    have hR : R < Real.log (a*y) := by
      apply Real.exp_lt_exp.mp
      rw [Real.exp_log (mul_pos ha hpos)]
      have h := (div_lt_iff₀ ha).mp hy
      linarith
    refine ⟨Real.log (a*y), hR, ?_⟩
    rw [Real.exp_log (mul_pos ha hpos)]
    field_simp [ha.ne']

theorem scaledExp_injective {a : ℝ} (ha : 0 < a) :
    Function.Injective (fun r : ℝ => Real.exp r/a) := by
  intro r s hrs
  apply Real.exp_injective
  have h := congrArg (fun t : ℝ => t*a) hrs
  simpa only [div_mul_cancel₀ _ ha.ne'] using h

theorem scaledExp_energy_density (c : ℝ → ℂ) {a : ℝ} (ha : 0 < a) (r : ℝ) :
    |Real.exp r/a| • heightEnergy c (Real.exp r/a) = ‖logarithmicMode c a r‖^2 := by
  have hy : 0 < Real.exp r/a := div_pos (Real.exp_pos r) ha
  rw [logarithmicMode, besselTransform, normalizedHeight_norm_sq c hy,
    abs_of_pos hy]
  dsimp [heightEnergy]
  rw [smul_eq_mul]
  field_simp [ha.ne', Real.exp_ne_zero r]

/-- The actual change-of-variables theorem proves integrability in both
directions, rather than merely comparing potentially default-zero integrals. -/
theorem logarithmicMode_sq_integrable_iff (c : ℝ → ℂ) {a : ℝ} (ha : 0 < a) (R : ℝ) :
    IntegrableOn (fun r => ‖logarithmicMode c a r‖^2) (Ioi R) ↔
      IntegrableOn (heightEnergy c) (Ioi (Real.exp R/a)) := by
  have h := integrableOn_image_iff_integrableOn_abs_deriv_smul
    (s := Ioi R) measurableSet_Ioi
    (fun r _ => ((Real.hasDerivAt_exp r).div_const a).hasDerivWithinAt)
    (scaledExp_injective ha).injOn (heightEnergy c)
  rw [scaledExp_image_Ioi ha R] at h
  simp_rw [scaledExp_energy_density c ha] at h
  exact h.symm

/-- Exact energy equality, with all scale factors and endpoints retained. -/
theorem logarithmicMode_sq_integral (c : ℝ → ℂ) {a : ℝ} (ha : 0 < a) (R : ℝ) :
    (∫ r in Ioi R, ‖logarithmicMode c a r‖^2) =
      ∫ y in Ioi (Real.exp R/a), heightEnergy c y := by
  have h := integral_image_eq_integral_abs_deriv_smul
    (s := Ioi R) measurableSet_Ioi
    (fun r _ => ((Real.hasDerivAt_exp r).div_const a).hasDerivWithinAt)
    (scaledExp_injective ha).injOn (heightEnergy c)
  rw [scaledExp_image_Ioi ha R] at h
  simp_rw [scaledExp_energy_density c ha] at h
  exact h.symm

theorem logarithmicMode_continuous {c : ℝ → ℂ}
    (hc : ContDiffOn ℝ 2 c (Ioi (0 : ℝ))) {a : ℝ} (ha : 0 < a) :
    Continuous (logarithmicMode c a) := by
  apply continuous_iff_continuousAt.mpr
  intro r
  exact ((besselTransform_hasDerivAt hc ha (Real.exp_pos r)).comp r
    (Real.hasDerivAt_exp r)).continuousAt

/-- Genuine raw hyperbolic height L2 produces the logarithmic L2 input
required by actual Bessel I/K classification. -/
theorem logarithmicMode_memLp_two {c : ℝ → ℂ}
    (hc : ContDiffOn ℝ 2 c (Ioi (0 : ℝ))) {a Y : ℝ} (ha : 0 < a) (hY : 0 < Y)
    (henergy : IntegrableOn (heightEnergy c) (Ioi Y)) :
    MemLp (logarithmicMode c a) 2 (volume.restrict (Ioi (Real.log (a*Y)))) := by
  apply (memLp_two_iff_integrable_sq_norm
    (logarithmicMode_continuous hc ha).aestronglyMeasurable.restrict).mpr
  apply (logarithmicMode_sq_integrable_iff c ha (Real.log (a*Y))).mpr
  simpa only [Real.exp_log (mul_pos ha hY), mul_div_cancel_left₀ _ ha.ne'] using henergy

theorem logarithmicMode_energy_exact (c : ℝ → ℂ) {a Y : ℝ} (ha : 0 < a) (hY : 0 < Y) :
    (∫ r in Ioi (Real.log (a*Y)), ‖logarithmicMode c a r‖^2) =
      ∫ y in Ioi Y, y⁻¹^2 * ‖c y‖^2 := by
  simpa only [Real.exp_log (mul_pos ha hY), mul_div_cancel_left₀ _ ha.ne', heightEnergy] using
    logarithmicMode_sq_integral c ha (Real.log (a*Y))

/-- Applied to the actual periodic Maass coefficient, with no regularity
of the coefficient assumed. Its C2 theorem is consumed here. -/
theorem actual_fourier_log_bessel_memLp {u : ℝ × ℝ → ℂ}
    (hu : ContDiffOn ℝ 2 u upperDomain) {n : ℤ} (hn : n ≠ 0) {Y : ℝ} (hY : 0 < Y)
    (henergy : IntegrableOn (fun y => y⁻¹^2 * ‖coefficient u n y‖^2) (Ioi Y)) :
    MemLp (fun r => actualBesselMode u n (Real.exp r)) 2
      (volume.restrict (Ioi (Real.log (modeFrequency n*Y)))) :=
  logarithmicMode_memLp_two (coefficient_contDiffOn_two hu n) (modeFrequency_pos hn) hY henergy

/-- Literal-cell dictionary for the existing circle Parseval bound. -/
theorem coefficient_norm_sq_le_slice {u : ℝ × ℝ → ℂ}
    (hu : ContinuousOn u upperDomain) (n : ℤ) {y : ℝ} (hy : 0 < y) :
    ‖coefficient u n y‖^2 ≤ ∫ x : PeriodCell, ‖u (x,y)‖^2 := by
  have hslice := continuous_slice hu hy
  have hsq : IntegrableOn (fun x => ‖u (x,y)‖^2) (Ioc (0 : ℝ) 1) :=
    ((hslice.norm.pow 2).intervalIntegrable 0 1).1
  have hlp : MemLp (fun x => u (x,y)) 2 (volume.restrict (Ioc (0 : ℝ) 1)) :=
    (memLp_two_iff_integrable_sq_norm hslice.aestronglyMeasurable.restrict).mpr hsq
  have hs := AddCircle.hasSum_sq_fourierCoeffOn (by norm_num : (0 : ℝ) < 1) hlp
  have hb := hs.summable.le_tsum n (fun m _ => sq_nonneg _)
  rw [hs.tsum_eq] at hb
  rw [coefficient_eq_fourierCoeffOn, integral_subtype_comap measurableSet_Icc,
    integral_Icc_eq_integral_Ioc]
  simpa only [sub_zero, inv_one, one_smul,
    intervalIntegral.integral_of_le zero_le_one] using hb

/-- True raw spatial cusp-strip L2, not a coefficient-L2 hypothesis, pays
for coefficient height energy via Parseval and product-measure Fubini. -/
theorem coefficient_heightEnergy_integrable_of_strip {u : ℝ × ℝ → ℂ}
    (hu : ContinuousOn u upperDomain) {Y : ℝ} (hY : 0 < Y)
    (hstrip : Integrable (fun p : PeriodCell × ℝ => p.2⁻¹^2 * ‖u (p.1,p.2)‖^2)
      ((volume : Measure PeriodCell).prod (volume.restrict (Ioi Y)))) (n : ℤ) :
    IntegrableOn (heightEnergy (coefficient u n)) (Ioi Y) := by
  have hcoef := coefficient_continuousOn hu n
  have hcont : ContinuousOn (heightEnergy (coefficient u n)) (Ioi Y) := by
    exact ((continuousOn_id.inv₀ (fun y hy => (hY.trans hy).ne')).pow 2).mul
      ((hcoef.mono (fun y hy => hY.trans hy)).norm.pow 2)
  apply hstrip.integral_prod_right.mono_nonneg (hcont.aestronglyMeasurable measurableSet_Ioi)
  · exact Filter.Eventually.of_forall (fun y => mul_nonneg (sq_nonneg _) (sq_nonneg _))
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with y hy
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left (coefficient_norm_sq_le_slice hu n (hY.trans hy)) (sq_nonneg _)

/-- End-to-end analytic tail transfer from the actual spatial strip norm.
No Fourier norm or transformed Bessel norm is supplied as a premise. -/
theorem actual_fourier_log_bessel_memLp_of_strip {u : ℝ × ℝ → ℂ}
    (hu : ContDiffOn ℝ 2 u upperDomain) {Y : ℝ} (hY : 0 < Y)
    (hstrip : Integrable (fun p : PeriodCell × ℝ => p.2⁻¹^2 * ‖u (p.1,p.2)‖^2)
      ((volume : Measure PeriodCell).prod (volume.restrict (Ioi Y))))
    {n : ℤ} (hn : n ≠ 0) :
    MemLp (fun r => actualBesselMode u n (Real.exp r)) 2
      (volume.restrict (Ioi (Real.log (modeFrequency n*Y)))) :=
  actual_fourier_log_bessel_memLp hu hn hY
    (coefficient_heightEnergy_integrable_of_strip hu.continuousOn hY hstrip n)

end
end ImbalancedChen.Part3.ActualFourierBesselLogL220261026a
