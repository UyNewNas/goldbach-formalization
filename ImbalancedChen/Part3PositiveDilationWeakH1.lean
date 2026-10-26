import ImbalancedChen.Part3GammaCompletedPlanarGradientBudget
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-! SOURCE_ONLY / UNCOMPILED / zero formal credit.
Positive uniform coordinate dilation is the actual width-diagonal part
of a normalized rational cusp chart. This source proves its weak chain
rule by transforming arbitrary compact tests, and proves exact planar
gradient-energy invariance. No normalized-frame H1 hypothesis is assumed. -/

namespace ImbalancedChen.Part3.PositiveDilationWeakH120261026b
noncomputable section
open Set MeasureTheory Filter
open scoped Topology Pointwise
open CompactC2ProductMollifier20261026a
open ActualPullbackLocalH1Transfer20261026b
open PlanarLocalWeakGradientExtraction20261026b

theorem dilation_quasiMeasurePreserving (a : ℝ) (ha : 0 < a) :
    QuasiMeasurePreserving (fun p : Plane => a • p) (volume : Measure Plane) volume := by
  refine ⟨(continuous_const_smul a).measurable,?_⟩
  exact Measure.absolutelyContinuous_of_le_smul
    (le_of_eq (Measure.map_addHaar_smul (volume : Measure Plane) ha.ne'))

theorem dilation_memLp (a : ℝ) (ha : 0 < a) {F : Plane → ℂ}
    (hF : MemLp F 2 (volume : Measure Plane)) :
    MemLp (fun p => F (a • p)) 2 (volume : Measure Plane) := by
  have hm := hF.aestronglyMeasurable.comp_quasiMeasurePreserving (dilation_quasiMeasurePreserving a ha)
  apply (memLp_two_iff_integrable_sq_norm hm).mpr
  exact (hF.integrable_norm_pow (by decide : (2 : ℕ) ≠ 0)).comp_smul ha.ne'

theorem dilation_integral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (a : ℝ) (ha : 0 < a) (F : Plane → E) :
    (∫ p : Plane, F (a • p)) = (a^2)⁻¹ • ∫ p : Plane, F p := by
  simpa [Module.finrank_prod] using
    Measure.integral_comp_smul_of_nonneg (volume : Measure Plane) F a (hR := ha.le)

def inverseTest (a : ℝ) (ψ : Plane → ℂ) (q : Plane) : ℂ := ψ (a⁻¹ • q)

theorem inverseTest_directional (a : ℝ) (ψ : Plane → ℂ) (hψ : ContDiff ℝ ∞ ψ)
    (v q : Plane) :
    directional v (inverseTest a ψ) q = a⁻¹ • directional v ψ (a⁻¹ • q) := by
  have hd := ((hψ.differentiable (by norm_num) (a⁻¹ • q)).hasFDerivAt.comp q
    ((a⁻¹ • ContinuousLinearMap.id ℝ Plane).hasFDerivAt)).fderiv
  unfold directional inverseTest
  rw [hd]
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply,map_smul]

theorem inverseTest_tsupport (a : ℝ) (ha : 0 < a) (ψ : Plane → ℂ) :
    tsupport (inverseTest a ψ) = (fun q : Plane => a⁻¹ • q) ⁻¹' tsupport ψ := by
  exact tsupport_comp_eq_preimage ψ (Homeomorph.smulOfNeZero a⁻¹ (inv_ne_zero ha.ne'))

/-- Literal distributional chain rule: the transformed weak derivative
is a times the original derivative at a*p. The proof transforms the
compact test, retaining the actual dimension-two Jacobian. -/
theorem local_weak_identity_dilation (a : ℝ) (ha : 0 < a)
    {Ω Q : Set Plane} (hsub : a • Q ⊆ Ω) (F G : Plane → ℂ) (v : Plane)
    (hweak : ∀ ψ : Plane → ℂ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ Ω →
      (∫ p, star (ψ p)*G p) = -(∫ p, star (directional v ψ p)*F p))
    {ψ : Plane → ℂ} (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ) (hs : tsupport ψ ⊆ Q) :
    (∫ p, star (ψ p)*(a • G (a • p))) =
      -(∫ p, star (directional v ψ p)*F (a • p)) := by
  let φ := inverseTest a ψ
  have hφ : ContDiff ℝ ∞ φ := hψ.comp (contDiff_const.smul contDiff_id)
  have hφc : HasCompactSupport φ := hc.comp_smul (inv_ne_zero ha.ne')
  have hφΩ : tsupport φ ⊆ Ω := by
    intro q hq
    have hq' : a⁻¹ • q ∈ tsupport ψ := by
      simpa only [φ,inverseTest_tsupport a ha,mem_preimage] using hq
    apply hsub
    exact ⟨a⁻¹ • q,hs hq',by simp only [smul_smul,mul_inv_cancel₀ ha.ne',one_smul]⟩
  have hold := hweak φ hφ hφc hφΩ
  have hvalue (p : Plane) : φ (a • p) = ψ p := by
    simp only [φ,inverseTest,smul_smul,inv_mul_cancel₀ ha.ne',one_smul]
  have hmass : (∫ p, star (directional v ψ p)*F (a • p)) =
      a • ((a^2)⁻¹ • ∫ q, star (directional v φ q)*F q) := by
    calc
      _ = ∫ p, a • (star (directional v φ (a • p))*F (a • p)) := by
        apply integral_congr_ae
        exact Eventually.of_forall (fun p => by
          rw [inverseTest_directional a ψ hψ]
          simp [smul_smul,ha.ne',smul_mul_assoc])
      _ = _ := by rw [integral_smul,dilation_integral a ha]
  calc
    (∫ p, star (ψ p)*(a • G (a • p))) =
        a • (∫ p, star (φ (a • p))*G (a • p)) := by
      rw [← integral_smul]
      apply integral_congr_ae
      exact Eventually.of_forall (fun p => by rw [hvalue]; simp only [mul_smul_comm])
    _ = a • ((a^2)⁻¹ • ∫ q, star (φ q)*G q) := by rw [dilation_integral a ha]
    _ = -(a • ((a^2)⁻¹ • ∫ q, star (directional v φ q)*F q)) := by rw [hold]; simp
    _ = _ := by rw [← hmass]

/-- Genuine local H1 is transported through the positive width dilation.
The scalar local L2 condition is proved from a measurable indicator
extension, while the two derivative classes are actual global L2 pulls. -/
theorem coordinate_local_H1_dilation (a : ℝ) (ha : 0 < a)
    {Ω Q : Set Plane} (hΩ : MeasurableSet Ω) (hQ : MeasurableSet Q)
    (hsub : a • Q ⊆ Ω) {F : Plane → ℂ} (hF : HasCoordinateLocalH1On Ω F) :
    HasCoordinateLocalH1On Q (fun p => F (a • p)) := by
  obtain ⟨hF,gx,gy,hgrad⟩ := hF
  have hglobal := (memLp_indicator_iff_restrict hΩ).2 hF
  have hscaled := (dilation_memLp a ha hglobal).restrict Q
  have hvalue : MemLp (fun p => F (a • p)) 2 ((volume : Measure Plane).restrict Q) := by
    apply hscaled.ae_eq
    filter_upwards [ae_restrict_mem hQ] with p hp
    exact Set.indicator_of_mem (hsub ⟨p,hp,rfl⟩) F
  have hx := (dilation_memLp a ha gx.memLp).const_smul a
  have hy := (dilation_memLp a ha gy.memLp).const_smul a
  refine ⟨hvalue,hx.toLp _,hy.toLp _,?_⟩
  intro ψ hψ hc hs
  have hX := local_weak_identity_dilation a ha hsub F gx ex
    (fun ψ hψ hc hs => (hgrad ψ hψ hc hs).1) hψ hc hs
  have hY := local_weak_identity_dilation a ha hsub F gy ey
    (fun ψ hψ hc hs => (hgrad ψ hψ hc hs).2) hψ hc hs
  constructor
  · have he : (∫ p, star (ψ p)*hx.toLp (fun q => a • gx (a • q)) p) =
        ∫ p, star (ψ p)*(a • gx (a • p)) := by
      apply integral_congr_ae
      filter_upwards [hx.coeFn_toLp] with p hp
      rw [hp]
    rw [he]
    exact hX
  · have he : (∫ p, star (ψ p)*hy.toLp (fun q => a • gy (a • q)) p) =
        ∫ p, star (ψ p)*(a • gy (a • p)) := by
      apply integral_congr_ae
      filter_upwards [hy.coeFn_toLp] with p hp
      rw [hp]
    rw [he]
    exact hY

/-- The two-dimensional derivative factor a² cancels exactly against
the planar dilation Jacobian a^-2. -/
theorem dilated_derivative_energy (a : ℝ) (ha : 0 < a) (G : Plane → ℂ) :
    (∫ p : Plane, ‖a • G (a • p)‖^2) = ∫ p : Plane, ‖G p‖^2 := by
  simp_rw [norm_smul,Real.norm_eq_abs,mul_pow,sq_abs]
  rw [integral_const_mul,dilation_integral a ha]
  change a^2*((a^2)⁻¹ * _) = _
  field_simp [ha.ne']

end
end ImbalancedChen.Part3.PositiveDilationWeakH120261026b
