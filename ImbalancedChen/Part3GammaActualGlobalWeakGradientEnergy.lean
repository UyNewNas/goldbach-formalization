import ImbalancedChen.Part3GammaActualWeakPartialCarrierEnergy

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
One pair of genuine ordinary weak derivatives on the entire upper chart
represents the native completed carrier gradient and the full form energy.
The comparison is proved by open-test uniqueness, canonical chart QMP,
and a countable positive rectangle cover. Global ordinary L2 and scalar
quotient descent of coordinate components are never asserted.
-/

namespace ImbalancedChen.Part3.GammaActualGlobalWeakGradientEnergy20261026b
noncomputable section
open Set Filter MeasureTheory
open scoped UpperHalfPlane
open ProductConvolutionSecondDerivatives20261026a PlanarLocalWeakGradientExtraction20261026b
open Gamma0ActualSmoothQuotientCore20261025a Gamma0ActualEnergyCompletion20261025a
open Gamma0ActualFriedrichsOperator20261025a Gamma0PhysicalClosedDirichletForm20261025a
open Gamma0FiniteMeasureCarrier20261024z Gamma0CarrierGradientHilbertMap20261026b
open Gamma0CarrierGradientExhaustion20261026b Gamma0EnergyGeometricWeakGradient20261025a
open ActualPullbackLocalH1Transfer20261026b WholeUpperChartWeakH1Patching20261026b
open LocalL2WeakGradientUniqueness20261026b GammaActualFormWholeChartH120261026b
open GammaCompletedGradientClassicalRepresentative20261026b
open GammaActualWeakPartialCarrierEnergy20261026b UpperRectangleMollifierGeometry20261026b
open Gamma0CompactDefectMollifier20261026a CanonicalPlanarL2UnitarySourceOnly
open ArbitraryCompactFirstGradientIBP20261026b CompactC2ProductMollifier20261026a
open CanonicalTensorHyperbolicLaplacianForm20261024z

/-- Comparison with a merely LOCAL L2 derivative. Indicator extension
is used only for uniqueness; the original derivative is retained on U. -/
theorem partial_eq_local_weak_component (N : ℕ) [NeZero N]
    {K : Set UpperHalfPlane} (hK : IsCompact K) (e : EnergyCompletion N)
    (vertical : Bool) {U R : Set Plane} (hU : IsOpen U) (hR : MeasurableSet R)
    (hUR : U ⊆ R) (hUp : U ⊆ MaassWeakOperatorCore20261024zz.positiveChart)
    (hUK : ∀ z : UpperHalfPlane, (z.re,z.im) ∈ U → z ∈ K)
    (G : Plane → ℂ) (hG : MemLp G 2 ((volume : Measure Plane).restrict R))
    (hw : ∀ ψ : Plane → ℂ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ U →
      (∫ p, star (ψ p) * G p) = -(∫ p,
        star (directional (coordinateDirection vertical) ψ p) *
          actualPlanePullback N (physicalProjection N e) p)) :
    ∀ᵐ p ∂(volume : Measure Plane), p ∈ U →
      planarCompletedPartial N hK vertical e p = G p := by
  have hi : MemLp (R.indicator G) 2 (volume : Measure Plane) :=
    (memLp_indicator_iff_restrict hR).2 hG
  have hp := planarCompletedPartial_memLp N hK vertical e
  let g : PlaneL2 := hi.toLp (R.indicator G)
  let q : PlaneL2 := hp.toLp (planarCompletedPartial N hK vertical e)
  have hg (ψ : Plane → ℂ) (hψ : ContDiff ℝ ∞ ψ)
      (hc : HasCompactSupport ψ) (hs : tsupport ψ ⊆ U) :
      (∫ p, star (ψ p) * g p) = -(∫ p,
        star (directional (coordinateDirection vertical) ψ p) *
          actualPlanePullback N (physicalProjection N e) p) := by
    rw [← hw ψ hψ hc hs]
    apply integral_congr_ae
    filter_upwards [hi.coeFn_toLp] with p hpi
    change (hi.toLp (R.indicator G)) p = R.indicator G p at hpi
    rw [show g p = R.indicator G p from hpi]
    by_cases hps : p ∈ tsupport ψ
    · rw [Set.indicator_of_mem (hUR (hs hps))]
    · simp [image_eq_zero_of_notMem_tsupport hps]
  have hq (ψ : Plane → ℂ) (hψ : ContDiff ℝ ∞ ψ)
      (hc : HasCompactSupport ψ) (hs : tsupport ψ ⊆ U) :
      (∫ p, star (ψ p) * q p) = -(∫ p,
        star (directional (coordinateDirection vertical) ψ p) *
          actualPlanePullback N (physicalProjection N e) p) := by
    have he := planarCompletedPartial_weak_for_representative N hK vertical e hUp hUK
      (actualPlanePullback N (physicalProjection N e))
      (Eventually.of_forall (fun z =>
        (actualPlanePullback_at_upper N (physicalProjection N e) z).symm)) hψ hc hs
    refine (integral_congr_ae ?_).trans he
    filter_upwards [hp.coeFn_toLp] with p hpi
    rw [show q p = planarCompletedPartial N hK vertical e p from hpi]
  have heq := local_component_unique hU
    (actualPlanePullback N (physicalProjection N e)) (coordinateDirection vertical) q g hq hg
  filter_upwards [heq,hi.coeFn_toLp,hp.coeFn_toLp] with p he hgi hqi
  intro hpin
  have ht := he hpin
  change (hp.toLp (planarCompletedPartial N hK vertical e)) p =
    (hi.toLp (R.indicator G)) p at ht
  rw [hqi,hgi,Set.indicator_of_mem (hUR hpin)] at ht
  exact ht

def globalRawGradientEnergy (Gx Gy : Plane → ℂ) (z : UpperHalfPlane) : ℝ :=
  z.im^2 * (‖Gx (z.re,z.im)‖^2 + ‖Gy (z.re,z.im)‖^2)

/-- The SAME whole-chart derivative witnesses represent the global
carrier gradient. Their mere local L2 regularity suffices for uniqueness. -/
theorem completed_global_raw_gradient_identification (N : ℕ) [NeZero N]
    (e : EnergyCompletion N) (Gx Gy : Plane → ℂ)
    (hloc : ∀ K : Set Plane, IsCompact K → K ⊆ upperChart →
      MemLp (actualPlanePullback N (physicalProjection N e)) 2 (volume.restrict K) ∧
      MemLp Gx 2 (volume.restrict K) ∧ MemLp Gy 2 (volume.restrict K))
    (hw : ∀ ψ : Plane → ℂ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ upperChart →
      ((∫ p, star (ψ p) * Gx p) = -(∫ p,
        star (directional xDirection ψ p) * actualPlanePullback N (physicalProjection N e) p)) ∧
      ((∫ p, star (ψ p) * Gy p) = -(∫ p,
        star (directional yDirection ψ p) * actualPlanePullback N (physicalProjection N e) p))) :
    ∀ᵐ z ∂carrierVolume N,
      (completedCarrierGradient N e) z 0 = (z.im : ℂ) * Gx (z.re,z.im) ∧
      (completedCarrierGradient N e) z 1 = (z.im : ℂ) * Gy (z.re,z.im) := by
  have hper (n : ℕ) : ∀ᵐ z ∂carrierVolume N, (z.re,z.im) ∈ chartRectangle n →
      (completedCarrierGradient N e) z 0 = (z.im : ℂ) * Gx (z.re,z.im) ∧
      (completedCarrierGradient N e) z 1 = (z.im : ℂ) * Gy (z.re,z.im) := by
    let R : Set Plane := Icc (-((n : ℝ)+1)) ((n : ℝ)+1) ×ˢ
      Icc (mollifierRadius (n+1)) ((n : ℝ)+1)
    let K := upperRectangle (-((n : ℝ)+1)) ((n : ℝ)+1)
      (mollifierRadius (n+1)) ((n : ℝ)+1)
    have hK : IsCompact K := upperRectangle_isCompact _ _ _ _ (mollifierRadius_pos (n+1))
    have hUR : chartRectangle n ⊆ R := fun p hp =>
      ⟨⟨hp.1.1.le,hp.1.2.le⟩,hp.2.1.le,hp.2.2.le⟩
    have hRp : R ⊆ upperChart := fun p hp => (mollifierRadius_pos (n+1)).trans_le hp.2.1
    have hUp : chartRectangle n ⊆ upperChart := hUR.trans hRp
    have hUK : ∀ z : UpperHalfPlane, (z.re,z.im) ∈ chartRectangle n → z ∈ K :=
      fun z hz => hUR hz
    have hR : IsCompact R := isCompact_Icc.prod isCompact_Icc
    have hx := partial_eq_local_weak_component N hK e false (chartRectangle_open n)
      hR.measurableSet hUR hUp hUK Gx (hloc R hR hRp).2.1
      (fun ψ hψ hc hs => by
        simpa [coordinateDirection,ex,xDirection] using (hw ψ hψ hc (hs.trans hUp)).1)
    have hy := partial_eq_local_weak_component N hK e true (chartRectangle_open n)
      hR.measurableSet hUR hUp hUK Gy (hloc R hR hRp).2.2
      (fun ψ hψ hc hs => by
        simpa [coordinateDirection,ey,yDirection] using (hw ψ hψ hc (hs.trans hUp)).2)
    have hxH := chartMap_quasiMeasurePreserving.ae hx
    have hyH := chartMap_quasiMeasurePreserving.ae hy
    have hxc : ∀ᵐ z ∂(carrierVolume N).restrict K,
        (completedCarrierGradient N e) z 0 =
          (z.im : ℂ) * planarCompletedPartial N hK false e (z.re,z.im) := by
      change ∀ᵐ z ∂((volume : Measure UpperHalfPlane).restrict (gamma0Carrier N)).restrict K, _
      rw [Measure.restrict_restrict hK.measurableSet,inter_comm]
      exact completedCarrierGradient_eq_height_partial N hK e false
    have hyc : ∀ᵐ z ∂(carrierVolume N).restrict K,
        (completedCarrierGradient N e) z 1 =
          (z.im : ℂ) * planarCompletedPartial N hK true e (z.re,z.im) := by
      change ∀ᵐ z ∂((volume : Measure UpperHalfPlane).restrict (gamma0Carrier N)).restrict K, _
      rw [Measure.restrict_restrict hK.measurableSet,inter_comm]
      exact completedCarrierGradient_eq_height_partial N hK e true
    have hcx := (ae_restrict_iff' hK.measurableSet).mp hxc
    have hcy := (ae_restrict_iff' hK.measurableSet).mp hyc
    filter_upwards [ae_restrict_of_ae hxH,ae_restrict_of_ae hyH,hcx,hcy] with z hxz hyz hcxz hcyz
    intro hz
    exact ⟨(hcxz (hUK z hz)).trans (congrArg ((z.im : ℂ) * ·) (hxz hz)),
      (hcyz (hUK z hz)).trans (congrArg ((z.im : ℂ) * ·) (hyz hz))⟩
  have hall : ∀ᵐ z ∂carrierVolume N, ∀ n : ℕ, (z.re,z.im) ∈ chartRectangle n →
      (completedCarrierGradient N e) z 0 = (z.im : ℂ) * Gx (z.re,z.im) ∧
      (completedCarrierGradient N e) z 1 = (z.im : ℂ) * Gy (z.re,z.im) := ae_all_iff.2 hper
  filter_upwards [hall] with z hz
  have hzU : (z.re,z.im) ∈ upperChart := z.im_pos
  rw [← chartRectangle_cover] at hzU
  obtain ⟨n,hn⟩ := mem_iUnion.mp hzU
  exact hz n hn

/-- A single global weak gradient of every EXISTING formvector has
honest global carrier energy, equal to the original closed form. -/
theorem completed_has_global_raw_gradient_energy (N : ℕ) [NeZero N]
    (e : EnergyCompletion N) :
    ∃ Gx Gy : Plane → ℂ,
      (∀ K : Set Plane, IsCompact K → K ⊆ upperChart →
        MemLp (actualPlanePullback N (physicalProjection N e)) 2 (volume.restrict K) ∧
        MemLp Gx 2 (volume.restrict K) ∧ MemLp Gy 2 (volume.restrict K)) ∧
      (∀ ψ : Plane → ℂ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ upperChart →
        ((∫ p, star (ψ p) * Gx p) = -(∫ p,
          star (directional xDirection ψ p) * actualPlanePullback N (physicalProjection N e) p)) ∧
        ((∫ p, star (ψ p) * Gy p) = -(∫ p,
          star (directional yDirection ψ p) * actualPlanePullback N (physicalProjection N e) p))) ∧
      Integrable (globalRawGradientEnergy Gx Gy) (carrierVolume N) ∧
      (actualDirichletPair N e e).re = ∫ z, globalRawGradientEnergy Gx Gy z ∂carrierVolume N := by
  obtain ⟨Gx,Gy,hloc,hw⟩ := completed_whole_upperChart_H1 N e
  have hG := completed_global_raw_gradient_identification N e Gx Gy hloc hw
  have heq : (fun z => ‖completedCarrierGradient N e z‖^2) =ᵐ[carrierVolume N]
      globalRawGradientEnergy Gx Gy := by
    filter_upwards [hG] with z hz
    rw [EuclideanSpace.norm_sq_eq,Fin.sum_univ_two,hz.1,hz.2]
    simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos z.im_pos,mul_pow]
    unfold globalRawGradientEnergy
    ring
  refine ⟨Gx,Gy,hloc,hw,(completedCarrierGradient_integrable_norm_sq N e).congr heq,?_⟩
  exact (actualDirichletPair_eq_carrier_gradient_integral N e).trans (integral_congr_ae heq)

end
end ImbalancedChen.Part3.GammaActualGlobalWeakGradientEnergy20261026b
