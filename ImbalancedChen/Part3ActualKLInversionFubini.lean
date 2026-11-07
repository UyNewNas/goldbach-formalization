import ImbalancedChen.Part3ActualKLInversionContinuity
import ImbalancedChen.Part3ActualGreenBoundaryDiagonal

/-!
Actual compact-test Fubini for the absolutely convergent KL inversion
integral. A single explicit integrable product majorant is obtained from
the radial support of the test and the actual third-transfer tau tail.
The resulting transform pairing is an identity of literal integrals.
No Plancherel or inversion equality is a premise.
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.
-/

namespace ImbalancedChen.Part3.ActualKLInversionFubini20261025a

noncomputable section
open Set MeasureTheory Filter
open scoped Topology
open RadialSchrodingerL2Form20261025a ComplexOrderKBridgeSourceOnly
open ComplexOrderKRadialRegularitySourceOnly ActualKLCompactTestIntegrationByParts20261025a
open ActualKLCompactTestWeightedL220261025a ActualKLInversionBounds20261025a
open ActualKLInversionContinuity20261025a ActualGreenBoundaryMajorant20261025a
open ActualGreenBoundaryDiagonal20261025a

theorem inversionTestJoint_stronglyMeasurable (T : RadialTest)
    {g : ℝ → ℂ} (hg : Continuous g) :
    StronglyMeasurable (fun p : ℝ × ℝ =>
      actualKLInversionIntegrand T p.2 p.1 * star (g p.2)) := by
  have hbase : Continuous (fun p : (ℝ × ℝ) × ℝ =>
      complexOrderIntegrand ((p.1.1 : ℂ) * Complex.I) (Real.exp p.1.2) p.2) := by
    unfold complexOrderIntegrand
    fun_prop
  have hk : StronglyMeasurable (fun p : ℝ × ℝ =>
      radialK ((p.1 : ℂ) * Complex.I) p.2) :=
    hbase.stronglyMeasurable.integral_prod_right'
      (ν := (volume : Measure ℝ).restrict (Ioi (0 : ℝ)))
  have hw : Continuous (fun p : ℝ × ℝ => (actualKLWeight p.1 : ℂ)) := by
    unfold actualKLWeight normalization
    fun_prop
  exact (((hw.stronglyMeasurable.mul
    ((actualKtransform_stronglyMeasurable T).comp_measurable measurable_fst)).mul hk).mul
      ((hg.comp continuous_snd).star.stronglyMeasurable))

/-- Absolute integrability on the full spectral/spatial product, including
the actual compact test factor. This is the Fubini prerequisite. -/
theorem inversionTestJoint_integrable (T : RadialTest)
    {g : ℝ → ℂ} (hg : Continuous g) (hgc : HasCompactSupport g) :
    Integrable (fun p : ℝ × ℝ => actualKLInversionIntegrand T p.2 p.1 * star (g p.2))
      (((volume : Measure ℝ).restrict (Ioi (0 : ℝ))).prod volume) := by
  obtain ⟨a0, ha0, hs0⟩ := exists_positive_physical_lower T
  obtain ⟨L, hL⟩ := hgc.bddBelow
  let a : ℝ := min a0 (Real.exp L)
  have ha : 0 < a := lt_min ha0 (Real.exp_pos L)
  have hs : ∀ r ∈ tsupport T.function, a ≤ Real.exp r :=
    fun r hr => (min_le_left _ _).trans (hs0 r hr)
  have hgInt : Integrable (fun r : ℝ => ‖g r‖) :=
    (hg.integrable_of_hasCompactSupport hgc).norm
  have hmajor := (inversionMajorant_integrable T a).mul_prod hgInt
  apply hmajor.mono' (inversionTestJoint_stronglyMeasurable T hg).aestronglyMeasurable
  have hpos : ∀ᵐ p : ℝ × ℝ
      ∂(((volume : Measure ℝ).restrict (Ioi (0 : ℝ))).prod volume), 0 < p.1 :=
    quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Ioi)
  filter_upwards [hpos] with p hp
  rw [norm_mul, norm_star]
  by_cases hz : g p.2 = 0
  · simp only [hz, norm_zero, mul_zero]
  have hr : a ≤ Real.exp p.2 := (min_le_right _ _).trans
    (Real.exp_le_exp.mpr (hL (subset_tsupport g hz)))
  exact mul_le_mul_of_nonneg_right
    (actualKLInversionIntegrand_norm_le_majorant T ha hs hr hp) (norm_nonneg _)

theorem actualKLInverse_test_integrable (T : RadialTest)
    {g : ℝ → ℂ} (hg : Continuous g) (hgc : HasCompactSupport g) :
    Integrable (fun r : ℝ => actualKLInverse T r * star (g r)) := by
  have h := (inversionTestJoint_integrable T hg hgc).integral_prod_right
  simpa only [actualKLInverse, integral_mul_const] using h

private theorem inversionTest_spatial_integral (T : RadialTest) (g : ℝ → ℂ) (tau : ℝ) :
    (∫ r : ℝ, actualKLInversionIntegrand T r tau * star (g r)) =
      (actualKLWeight tau : ℂ) * actualKtransform T.function tau *
        star (actualKtransform g tau) := by
  calc
    _ = ∫ r : ℝ, ((actualKLWeight tau : ℂ) * actualKtransform T.function tau) *
        (complexOrderK ((tau : ℂ) * Complex.I) (Real.exp r) * star (g r)) := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun r => by
        unfold actualKLInversionIntegrand radialK
        ring)
    _ = ((actualKLWeight tau : ℂ) * actualKtransform T.function tau) *
        rawRadialKTransform (fun r => star (g r)) tau := by
      rw [integral_const_mul]
      rfl
    _ = _ := by rw [rawRadialKTransform_star, rawRadialKTransform_eq_actualKtransform]

theorem actualKL_transform_pairing_integrable (T : RadialTest)
    {g : ℝ → ℂ} (hg : Continuous g) (hgc : HasCompactSupport g) :
    IntegrableOn (fun tau : ℝ => (actualKLWeight tau : ℂ) *
      actualKtransform T.function tau * star (actualKtransform g tau)) (Ioi (0 : ℝ)) := by
  have h := (inversionTestJoint_integrable T hg hgc).integral_prod_left
  simpa only [inversionTest_spatial_integral] using h

/-- The true inversion/test pairing, with product integrability supplied
above. The right side is the actual polarized transform integral. -/
theorem actualKLInverse_compact_test_pairing (T : RadialTest)
    {g : ℝ → ℂ} (hg : Continuous g) (hgc : HasCompactSupport g) :
    (∫ r : ℝ, actualKLInverse T r * star (g r)) =
      ∫ tau in Ioi (0 : ℝ), (actualKLWeight tau : ℂ) *
        actualKtransform T.function tau * star (actualKtransform g tau) := by
  calc
    _ = ∫ r : ℝ, ∫ tau in Ioi (0 : ℝ),
        actualKLInversionIntegrand T r tau * star (g r) := by
      simp only [actualKLInverse, integral_mul_const]
    _ = ∫ tau in Ioi (0 : ℝ), ∫ r : ℝ,
        actualKLInversionIntegrand T r tau * star (g r) :=
      (integral_integral_swap (inversionTestJoint_integrable T hg hgc)).symm
    _ = _ := by simp only [inversionTest_spatial_integral]

end
end ImbalancedChen.Part3.ActualKLInversionFubini20261025a
