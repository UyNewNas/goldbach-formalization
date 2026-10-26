import ImbalancedChen.Part3AERealChartPhysicalWeakTransfer

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

AE physical cylinder representatives lift to AE real-chart representatives.
The real-to-circle projection preserves null sets on the ENTIRE real line:
the genuine measure-preserving maps on all integer unit intervals and a
countable cover prove this, rather than asserting finite pushforward
measure for the infinite covering map. Product Fubini and the actual
positive-height subtype measure then give the real-chart AE identity.
-/
namespace ImbalancedChen.Part3.CuspCircleAELiftToRealChart20261026b
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
open CuspCylinderMeasure20261024z CuspZeroMeanEnergyOnlyTail20261025a
open ClosedHorizontalCuspTail20261026a SeparatedWeakCuspGraphApproximation20261026a
open ProductConvolutionSecondDerivatives20261026a RealChartToPhysicalCuspWeak20261026b
open CuspClassicalRawWeakTesting20261026b

attribute [local instance] Measure.Subtype.measureSpace
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : LocallyCompactSpace PositiveHeight := isOpen_Ioi.locallyCompactSpace
local instance : IsFiniteMeasureOnCompacts (volume : Measure PositiveHeight) :=
  IsFiniteMeasureOnCompacts.comap' volume continuous_subtype_val
    (MeasurableEmbedding.subtype_coe measurableSet_Ioi)
local instance : IsLocallyFiniteMeasure (volume : Measure PositiveHeight) := inferInstance
local instance : SigmaFinite (volume : Measure PositiveHeight) := inferInstance

/-- Global AE lifting is obtained by the true countable unit-interval
cover, not by a false measure-preserving infinite covering assertion. -/
theorem ae_circle_implies_ae_real {P : UnitAddCircle → Prop}
    (hP : ∀ᵐ x ∂AddCircle.haarAddCircle, P x) :
    ∀ᵐ t : ℝ, P (t : UnitAddCircle) := by
  have hcircle : ∀ᵐ x : UnitAddCircle ∂volume, P x := by
    simpa only [circleHaar_eq_volume] using hP
  have hk (k : ℤ) : ∀ᵐ t : ℝ, t ∈ Ioc (k : ℝ) ((k : ℝ) + 1) → P (t : UnitAddCircle) := by
    exact (ae_restrict_iff' measurableSet_Ioc).mp
      ((AddCircle.measurePreserving_mk (1 : ℝ) (k : ℝ)).quasiMeasurePreserving.ae hcircle)
  have hall : ∀ᵐ t : ℝ, ∀ k : ℤ, t ∈ Ioc (k : ℝ) ((k : ℝ) + 1) → P (t : UnitAddCircle) :=
    ae_all_iff.mpr hk
  filter_upwards [hall] with t ht
  obtain ⟨k, hk, huniq⟩ := existsUnique_sub_zsmul_mem_Ioc
    (show (0 : ℝ) < 1 by norm_num) t (0 : ℝ)
  have hkt : t ∈ Ioc (k : ℝ) ((k : ℝ) + 1) := by
    simp only [zsmul_eq_mul, mul_one, zero_add] at hk
    constructor <;> linarith [hk.1, hk.2]
  exact ht k hkt

theorem measurable_realCylinderLift {H : CuspCylinder → ℂ} (hH : Measurable H) :
    Measurable (realCylinderLift H) := by
  let S : Set Plane := {p : Plane | 0 < p.2}
  have hS : MeasurableSet S := (isOpen_lt continuous_const continuous_snd).measurableSet
  have hm : Measurable (fun p : S =>
      H (((p : Plane).1 : UnitAddCircle), ⟨(p : Plane).2, p.property⟩)) := by
    apply hH.comp
    exact (AddCircle.measurable_mk'.comp (measurable_fst.comp measurable_subtype_coe)).prodMk
      ((measurable_snd.comp measurable_subtype_coe).subtype_mk _)
  simpa only [realCylinderLift, S] using hm.dite measurable_const hS

/-- Native raw physical AE equality becomes REAL chart AE equality,
including all integer seams, on the actual positive tail. -/
theorem raw_physical_ae_real_lift {a : ℝ} (ha : 0 < a) {H J : CuspCylinder → ℂ}
    (hH : Measurable H) (hJ : Measurable J)
    (hHJ : H =ᵐ[derivativeMeasure a] J) :
    realCylinderLift H =ᵐ[(volume : Measure Plane).restrict {p : Plane | a < p.2}]
      realCylinderLift J := by
  rw [derivativeMeasure_product] at hHJ
  have hswap : ∀ᵐ p : PositiveHeight × UnitAddCircle
      ∂((volume : Measure PositiveHeight).restrict (strictHeightTail a)).prod
        (AddCircle.haarAddCircle (T := (1 : ℝ))), H (p.2, p.1) = J (p.2, p.1) :=
    (Measure.measurePreserving_swap.quasiMeasurePreserving).ae hHJ
  have hslices : ∀ᵐ y ∂(volume : Measure PositiveHeight).restrict (strictHeightTail a),
      ∀ᵐ x : ℝ, H ((x : UnitAddCircle), y) = J ((x : UnitAddCircle), y) := by
    filter_upwards [ae_ae_of_ae_prod hswap] with y hy
    exact ae_circle_implies_ae_real hy
  have hsub : ∀ᵐ y : PositiveHeight ∂(volume : Measure PositiveHeight), a < (y : ℝ) →
      ∀ᵐ x : ℝ, realCylinderLift H (x, (y : ℝ)) = realCylinderLift J (x, (y : ℝ)) := by
    have h := (ae_restrict_iff' (strictHeightTail_measurable a)).mp hslices
    simpa only [realCylinderLift_positive] using h
  have hypos : ∀ᵐ y : ℝ ∂(volume : Measure ℝ).restrict (Ioi (0 : ℝ)), a < y →
      ∀ᵐ x : ℝ, realCylinderLift H (x, y) = realCylinderLift J (x, y) :=
    (ae_restrict_iff_subtype measurableSet_Ioi).mpr hsub
  have hyall : ∀ᵐ y : ℝ, ∀ᵐ x : ℝ,
      a < y → realCylinderLift H (x, y) = realCylinderLift J (x, y) := by
    have h := (ae_restrict_iff' measurableSet_Ioi).mp hypos
    filter_upwards [h] with y hy
    by_cases hay : a < y
    · exact (hy (ha.trans hay) hay).mono fun x hx _ => hx
    · exact Eventually.of_forall fun x hx => False.elim (hay hx)
  have hm : MeasurableSet {p : Plane | a < p.2 → realCylinderLift H p = realCylinderLift J p} := by
    simpa only [imp_iff_not_or, setOf_or, setOf_not] using
      ((measurableSet_lt measurable_const measurable_snd).compl.union
        (measurableSet_eq_fun (measurable_realCylinderLift hH) (measurable_realCylinderLift hJ)))
  have hplane : ∀ᵐ p : Plane, a < p.2 → realCylinderLift H p = realCylinderLift J p :=
    (ae_prod_iff_ae_ae hm).mpr ((ae_ae_comm hm).mpr hyall)
  exact (ae_restrict_iff' (isOpen_lt continuous_const continuous_snd).measurableSet).mpr hplane

/-- Weighted-value AE equality has the same real-chart consequence by
the actual positive density, independently of any global norm bound. -/
theorem weighted_physical_ae_real_lift {a : ℝ} (ha : 0 < a) {H J : CuspCylinder → ℂ}
    (hH : Measurable H) (hJ : Measurable J)
    (hHJ : H =ᵐ[functionMeasure a] J) :
    realCylinderLift H =ᵐ[(volume : Measure Plane).restrict {p : Plane | a < p.2}]
      realCylinderLift J :=
  raw_physical_ae_real_lift ha hH hJ ((derivativeMeasure_ac_functionMeasure a).ae_eq hHJ)

end
end ImbalancedChen.Part3.CuspCircleAELiftToRealChart20261026b
