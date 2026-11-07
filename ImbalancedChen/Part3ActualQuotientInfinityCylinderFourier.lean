import ImbalancedChen.Part3ActualHighStripCylinderL2Equivalence
import ImbalancedChen.Part3ActualPoincareSpectralCoefficient

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Every original Gamma quotient L2 vector has a genuine contractive native
L2 realization on its HIGH infinity cusp cylinder. One common actual
height-AE set identifies all integer circle coefficients with the literal
original quotient Fourier integrals. Circle-slice L2 is derived by actual
product Fubini. No regularity of quotient representatives, Fourier-model
premise, all-cusp identification, or spectral expansion is assumed.
-/
namespace ImbalancedChen.Part3.ActualQuotientInfinityCylinderFourier20261026b

noncomputable section
open Set MeasureTheory Filter
open scoped UpperHalfPlane ENNReal
open Gamma0QuotientCellPushforward20261025a
open CuspCylinderMeasure20261024z
open ActualCuspStripCutoff20261025a
open CanonicalPlanarL2UnitarySourceOnly
open ActualPoincareSpectralCoefficient20261026a
open ActualInfinityHighTailL2Pullback20261026b
open ActualHighStripNativeCylinderMeasure20261026b
open ActualHighStripCylinderL2Equivalence20261026b

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

def actualQuotientInfinityCylinder (N : ℕ) [NeZero N] {Y : ℝ} (hY : 1 < Y) :
    QuotientL2 N →L[ℂ] CylinderTailL2 Y :=
  (highStripCylinderL2Equiv Y).toContinuousLinearEquiv.toContinuousLinearMap.comp
    (actualHighTailPullback N hY)

theorem actualQuotientInfinityCylinder_ae (N : ℕ) [NeZero N]
    {Y : ℝ} (hY : 1 < Y) (f : QuotientL2 N) :
    actualQuotientInfinityCylinder N hY f =ᵐ[
      cylinderMeasure.restrict (closedCylinderTail Y)]
      fun p => f (orbitProjection N (nativeCylinderPoint p)) := by
  have hp := (nativeCylinderPoint_measurePreserving Y).quasiMeasurePreserving.ae_eq
    (actualHighTailPullback_ae N hY f)
  exact (stripToCylinderIsometry_ae Y (actualHighTailPullback N hY f)).trans hp

theorem actualQuotientInfinityCylinder_norm_le (N : ℕ) [NeZero N]
    {Y : ℝ} (hY : 1 < Y) (f : QuotientL2 N) :
    ‖actualQuotientInfinityCylinder N hY f‖ ≤ ‖f‖ := by
  change ‖highStripCylinderL2Equiv Y (actualHighTailPullback N hY f)‖ ≤ ‖f‖
  rw [LinearIsometryEquiv.norm_map]
  exact actualHighTailPullback_norm_le N hY f

theorem actualQuotientInfinityCylinder_norm_eq (N : ℕ) [NeZero N]
    {Y : ℝ} (hY : 1 < Y) (f : QuotientL2 N) :
    ‖actualQuotientInfinityCylinder N hY f‖ =
      (eLpNorm f 2 ((carrierPushforward N).restrict
        (Gamma0ActualHighCuspTail20261025a.quotientHighTail N Y))).toReal := by
  change ‖highStripCylinderL2Equiv Y (actualHighTailPullback N hY f)‖ = _
  rw [LinearIsometryEquiv.norm_map, actualHighTailPullback_norm_eq]

def closedHeightTail (Y : ℝ) : Set PositiveHeight := {y | Y ≤ (y : ℝ)}

theorem closedHeightTail_measurable (Y : ℝ) : MeasurableSet (closedHeightTail Y) :=
  measurableSet_Ici.preimage measurable_subtype_coe

theorem closedCylinderTail_measure_product (Y : ℝ) :
    cylinderMeasure.restrict (closedCylinderTail Y) =
      AddCircle.haarAddCircle.prod (heightMeasure.restrict (closedHeightTail Y)) := by
  have hs : closedCylinderTail Y = univ ×ˢ closedHeightTail Y := by
    ext p
    simp [closedCylinderTail, closedHeightTail]
  rw [cylinderMeasure, hs, ← Measure.prod_restrict, Measure.restrict_univ]

def rawHeightPoint (x : ℝ) (y : PositiveHeight) : UpperHalfPlane :=
  ⟨⟨x, (y : ℝ)⟩, y.property⟩

theorem nativeCylinderPoint_coe (x : ℝ) (hx : x ∈ Ico (0 : ℝ) 1)
    (y : PositiveHeight) :
    nativeCylinderPoint ((x : UnitAddCircle), y) = rawHeightPoint x y := by
  apply UpperHalfPlane.ext
  apply Complex.ext
  · change ((AddCircle.equivIco (1 : ℝ) 0 (x : UnitAddCircle) :
      Ico (0 : ℝ) (0 + 1)) : ℝ) = x
    exact congrArg Subtype.val (AddCircle.equivIco_coe_eq (by simpa only [zero_add] using hx))
  · rfl

/-- Exact literal coefficient identity BEFORE passing to Lp classes.
The later theorem pays slice L2 and the representative AE join. -/
theorem quotient_circle_coefficient_eq_actualFourier (N : ℕ)
    (F : Gamma0OrbitSpace N → ℂ) (m : ℤ) (y : PositiveHeight) :
    AddCircle.fourierCoeff
      (fun x : UnitAddCircle => F (orbitProjection N (nativeCylinderPoint (x, y)))) m =
      actualTestFourier N F m (y : ℝ) := by
  let G : UnitAddCircle → ℂ := fun x =>
    AddCircle.fourier (-m) x * F (orbitProjection N (nativeCylinderPoint (x, y)))
  change (∫ x : UnitAddCircle, G x ∂AddCircle.haarAddCircle) = _
  rw [circleHaar_eq_volume]
  calc
    _ = ∫ x in Ioc (0 : ℝ) 1, G (x : UnitAddCircle) := by
      simpa only [zero_add] using (AddCircle.integral_preimage (1 : ℝ) (0 : ℝ) G).symm
    _ = ∫ x in Ico (0 : ℝ) 1, G (x : UnitAddCircle) := integral_Ico_eq_integral_Ioc.symm
    _ = _ := by
      rw [actualTestFourier]
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ico] with x hx
      have hp := chartPullback_at_upper (testLift N F) (rawHeightPoint x y)
      change chartPullback (testLift N F) (x, (y : ℝ)) =
        F (orbitProjection N (rawHeightPoint x y)) at hp
      simp only [G, nativeCylinderPoint_coe x hx y, hp]

/-- Product Fubini provides true L2 circle slices and a SINGLE height-AE
set valid for ALL original integer Fourier coefficients. -/
theorem actualQuotientInfinityCylinder_all_coefficients (N : ℕ) [NeZero N]
    {Y : ℝ} (hY : 1 < Y) (f : QuotientL2 N) :
    ∀ᵐ y ∂heightMeasure.restrict (closedHeightTail Y),
      MemLp (fun x : UnitAddCircle => actualQuotientInfinityCylinder N hY f (x, y))
        2 AddCircle.haarAddCircle ∧
      ∀ m : ℤ, AddCircle.fourierCoeff
          (fun x : UnitAddCircle => actualQuotientInfinityCylinder N hY f (x, y)) m =
        actualTestFourier N f m (y : ℝ) := by
  let U := actualQuotientInfinityCylinder N hY f
  have hsquare : Integrable (fun p : CuspCylinder => ‖U p‖ ^ 2)
      (AddCircle.haarAddCircle.prod (heightMeasure.restrict (closedHeightTail Y))) := by
    rw [← closedCylinderTail_measure_product]
    exact (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable U)).mp U.memLp
  have hae := actualQuotientInfinityCylinder_ae N hY f
  rw [closedCylinderTail_measure_product] at hae
  have hswap : ∀ᵐ p : PositiveHeight × UnitAddCircle
      ∂(heightMeasure.restrict (closedHeightTail Y)).prod AddCircle.haarAddCircle,
      U (p.2, p.1) = f (orbitProjection N (nativeCylinderPoint (p.2, p.1))) :=
    Measure.measurePreserving_swap.quasiMeasurePreserving.ae hae
  have hsections := ae_ae_of_ae_prod hswap
  filter_upwards [hsquare.prod_right_ae, hsections] with y hy hsec
  refine ⟨(memLp_two_iff_integrable_sq_norm
    ((Lp.stronglyMeasurable U).comp_measurable measurable_prodMk_right).aestronglyMeasurable).mpr hy,
      ?_⟩
  intro m
  rw [congrFun (AddCircle.fourierCoeff_congr_ae hsec) m]
  exact quotient_circle_coefficient_eq_actualFourier N f m y

end
end ImbalancedChen.Part3.ActualQuotientInfinityCylinderFourier20261026b
