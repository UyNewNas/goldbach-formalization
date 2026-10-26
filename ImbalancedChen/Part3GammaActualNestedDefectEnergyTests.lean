import ImbalancedChen.Part3GammaActualDefectSupportedFormTesting
import ImbalancedChen.Part3GammaActualClosedFormCutoffMultiplier

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
The supported native defect form test is identified with the square of
the ORIGINAL actual closed-form cutoff operator. Physical injectivity,
literal quotient multiplier representatives and actual cutoff nesting
prove the equality; no form-test/IMS identification is assumed.
-/

namespace ImbalancedChen.Part3.GammaActualNestedDefectEnergyTests20261026b
noncomputable section
open Set Filter MeasureTheory
open scoped UpperHalfPlane
open Gamma0QuotientCellPushforward20261025a Gamma0ActualSmoothQuotientCore20261025a
open Gamma0ActualMinimalShiftRange20261025a Gamma0ActualEnergyCompletion20261025a
open GammaActualDefectSupportedFormTesting20261026b GammaActualQuotientCutoffMultiplier20261026b
open GammaActualClosedFormCutoffMultiplier20261026b ActualModularSmoothCuspCutoff20261025a
open ActualModularSmoothCutoffL2Tail20261025a

theorem quotient_cutoff_nesting (N : ℕ) (Z Y : ℝ)
    (hnest : ∀ z : UpperHalfPlane, globalCutoff Z z * globalCutoff Y z = globalCutoff Y z)
    (q : Gamma0OrbitSpace N) :
    quotientCutoff N Z q * quotientCutoff N Y q = quotientCutoff N Y q :=
  Quotient.inductionOn q (fun z => hnest z)

theorem quotient_cutoff_nested_product (N : ℕ) [NeZero N] (Z Y : ℝ)
    (hZ : 1 < Z) (hY : 1 < Y)
    (hnest : ∀ z : UpperHalfPlane, globalCutoff Z z * globalCutoff Y z = globalCutoff Y z)
    (f : QuotientL2 N) :
    actualQuotientCutoffMultiplier N Y hY (actualQuotientCutoffMultiplier N Z hZ f) =
      actualQuotientCutoffMultiplier N Y hY f := by
  apply Lp.ext
  filter_upwards [actual_cutoff_product_literal_ae N Y hY (actualQuotientCutoffMultiplier N Z hZ f),
    actual_cutoff_product_literal_ae N Z hZ f,
    actual_cutoff_product_literal_ae N Y hY f] with q hleft houter hright
  rw [hleft,houter,hright]
  have hc : (quotientCutoff N Y q : ℂ) * (quotientCutoff N Z q : ℂ) =
      (quotientCutoff N Y q : ℂ) := by
    exact_mod_cast (mul_comm _ _).trans (quotient_cutoff_nesting N Z Y hnest q)
  rw [← mul_assoc,hc]

/-- The inner multiplier of the outer defect form lift is exactly the
unique original form lift of the inner cutoff times the defect. -/
theorem actual_defect_nested_cutoff_lift (N : ℕ) [NeZero N]
    (f : QuotientL2 N) (hf : f ∈ minimalShiftDefect N)
    (Z Y : ℝ) (hZ : 1 < Z) (hY : 1 < Y)
    (hnest : ∀ z : UpperHalfPlane, globalCutoff Z z * globalCutoff Y z = globalCutoff Y z) :
    actualClosedFormCutoff N Y hY (actualDefectCutoffEnergyLift N f hf Z hZ) =
      actualDefectCutoffEnergyLift N f hf Y hY := by
  apply physicalProjection_injective N
  rw [actualClosedFormCutoff_physical, actualDefectCutoffEnergyLift_projection,
    actualDefectCutoffEnergyLift_projection, quotient_cutoff_nested_product N Z Y hZ hY hnest]

theorem closed_cutoff_square_physical_ae (N : ℕ) [NeZero N]
    (Y : ℝ) (hY : 1 < Y) (e : EnergyCompletion N) :
    (physicalProjection N (actualClosedFormCutoff N Y hY (actualClosedFormCutoff N Y hY e)) :
      Gamma0OrbitSpace N → ℂ) =ᵐ[carrierPushforward N]
      fun q => (quotientCutoff N Y q : ℂ)^2 * physicalProjection N e q := by
  rw [actualClosedFormCutoff_physical, actualClosedFormCutoff_physical]
  filter_upwards [actual_cutoff_product_literal_ae N Y hY
    (actualQuotientCutoffMultiplier N Y hY (physicalProjection N e)),
    actual_cutoff_product_literal_ae N Y hY (physicalProjection N e)] with q hleft hright
  rw [hleft,hright]
  ring

theorem actual_defect_square_test_identification (N : ℕ) [NeZero N]
    (f : QuotientL2 N) (hf : f ∈ minimalShiftDefect N)
    (Z Y : ℝ) (hZ : 1 < Z) (hY : 1 < Y)
    (hnest : ∀ z : UpperHalfPlane, globalCutoff Z z * globalCutoff Y z = globalCutoff Y z)
    (e : EnergyCompletion N)
    (he : (physicalProjection N e : Gamma0OrbitSpace N → ℂ) =ᵐ[carrierPushforward N]
      fun q => (quotientCutoff N Y q : ℂ)^2 * f q) :
    e = actualClosedFormCutoff N Y hY
      (actualClosedFormCutoff N Y hY (actualDefectCutoffEnergyLift N f hf Z hZ)) := by
  apply physicalProjection_injective N
  apply Lp.ext
  have hout := actual_cutoff_product_literal_ae N Z hZ f
  rw [← actualDefectCutoffEnergyLift_projection N f hf Z hZ] at hout
  filter_upwards [he, closed_cutoff_square_physical_ae N Y hY
    (actualDefectCutoffEnergyLift N f hf Z hZ), hout] with q hleft hright houter
  rw [hleft,hright,houter]
  have hc : (quotientCutoff N Y q : ℂ)^2 * (quotientCutoff N Z q : ℂ) =
      (quotientCutoff N Y q : ℂ)^2 := by
    have hn : (quotientCutoff N Z q : ℂ) * (quotientCutoff N Y q : ℂ) =
        (quotientCutoff N Y q : ℂ) := by exact_mod_cast quotient_cutoff_nesting N Z Y hnest q
    calc
      _ = (quotientCutoff N Y q : ℂ) *
          ((quotientCutoff N Z q : ℂ) * (quotientCutoff N Y q : ℂ)) := by ring
      _ = _ := by rw [hn]; ring
  rw [← mul_assoc,hc]

/-- Actual shifted form testing in the EXACT operator form needed by
completed IMS. All support-controlled approximation and native testing
are supplied by the preceding proved construction. -/
theorem actual_defect_nested_shifted_form_test (N : ℕ) [NeZero N]
    (f : QuotientL2 N) (hf : f ∈ minimalShiftDefect N) (Y : ℝ) (hY : 1 < Y) :
    ∃ (Z : ℝ) (hZ : 1 < Z),
      (∀ z : UpperHalfPlane, globalCutoff Z z * globalCutoff Y z = globalCutoff Y z) ∧
      inner ℂ (actualDefectCutoffEnergyLift N f hf Z hZ)
        (actualClosedFormCutoff N Y hY (actualClosedFormCutoff N Y hY
          (actualDefectCutoffEnergyLift N f hf Z hZ))) = 0 := by
  obtain ⟨e,Z₀,hZ₀,hphysical,hall⟩ := actual_defect_cutoff_square_form_testing N f hf Y hY.le
  obtain ⟨hZ,htest,hnest⟩ := hall Z₀ (le_refl _)
  refine ⟨Z₀,hZ,hnest,?_⟩
  rw [← actual_defect_square_test_identification N f hf Z₀ Y hZ hY hnest e hphysical]
  exact htest

end
end ImbalancedChen.Part3.GammaActualNestedDefectEnergyTests20261026b
