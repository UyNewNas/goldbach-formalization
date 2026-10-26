import ImbalancedChen.Part3GammaGraphStrongLocalH1
import ImbalancedChen.Part3Gamma0CarrierGradientExhaustion

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Raw whole-chart coordinate fields with local L2 on every compact positive
set and FINITE LITERAL carrier energy give a native CarrierGradientL2.
Their global AE measurability is proved from the countable chart cover and
true chart quasi-measure-preservation. No measurability, form-domain,
existing completed-gradient or gradient-limit premise is supplied. -/

namespace ImbalancedChen.Part3.GammaRawWeightedFiberL220261026b
noncomputable section
open Set Filter MeasureTheory
open scoped Topology UpperHalfPlane
open ProductConvolutionSecondDerivatives20261026a
open CanonicalTensorHyperbolicLaplacianForm20261024z CanonicalPlanarL2UnitarySourceOnly
open Gamma0CompactCoreGradient20261025a Gamma0CarrierGradientHilbertMap20261026b
open WholeUpperChartWeakH1Patching20261026b Gamma0CompactDefectMollifier20261026a

def LocallyL2OnUpperChart (G : Plane → ℂ) : Prop :=
  ∀ K : Set Plane, IsCompact K → K⊆upperChart →
    MemLp G 2 ((volume : Measure Plane).restrict K)

theorem locallyL2_upperChart_aestronglyMeasurable (G : Plane → ℂ)
    (hG : LocallyL2OnUpperChart G) :
    AEStronglyMeasurable G ((volume : Measure Plane).restrict upperChart) := by
  rw [← chartRectangle_cover,aestronglyMeasurable_iUnion_iff]
  intro n
  let K : Set Plane := Icc (-((n : ℝ)+1)) ((n : ℝ)+1) ×ˢ
    Icc (mollifierRadius (n+1)) ((n : ℝ)+1)
  have hK : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hs : K⊆upperChart := fun p hp => (mollifierRadius_pos (n+1)).trans_le hp.2.1
  have hsub : chartRectangle n⊆K := fun p hp =>
    ⟨⟨hp.1.1.le,hp.1.2.le⟩,hp.2.1.le,hp.2.2.le⟩
  exact ((hG K hK hs).mono_measure (Measure.restrict_mono_set volume hsub)).aestronglyMeasurable

theorem locallyL2_chart_pullback_aestronglyMeasurable (G : Plane → ℂ)
    (hG : LocallyL2OnUpperChart G) :
    AEStronglyMeasurable (fun z : UpperHalfPlane => G (chartMap z)) volume := by
  have hi := (aestronglyMeasurable_indicator_iff upperChart_measurable).2
    (locallyL2_upperChart_aestronglyMeasurable G hG)
  have hc := hi.comp_quasiMeasurePreserving chartMap_quasiMeasurePreserving
  apply hc.congr
  exact Eventually.of_forall fun z => by
    exact Set.indicator_of_mem (show chartMap z∈upperChart from z.im_pos) G

def rawWeightedFiber (Gx Gy : Plane → ℂ) (z : UpperHalfPlane) : GradientFiber :=
  (z.im : ℂ) • !₂[Gx (chartMap z),Gy (chartMap z)]

def rawCarrierEnergy (Gx Gy : Plane → ℂ) (z : UpperHalfPlane) : ℝ :=
  z.im^2*(‖Gx (chartMap z)‖^2+‖Gy (chartMap z)‖^2)

theorem rawWeightedFiber_norm_sq (Gx Gy : Plane → ℂ) (z : UpperHalfPlane) :
    ‖rawWeightedFiber Gx Gy z‖^2=rawCarrierEnergy Gx Gy z := by
  rw [rawWeightedFiber,norm_smul,mul_pow,EuclideanSpace.norm_sq_eq,Fin.sum_univ_two]
  simp only [Complex.norm_real,Real.norm_eq_abs,abs_of_pos z.im_pos,PiLp.toLp_apply,
    Matrix.cons_val_zero,Matrix.cons_val_one,rawCarrierEnergy]

theorem rawWeightedFiber_aestronglyMeasurable (Gx Gy : Plane → ℂ)
    (hx : LocallyL2OnUpperChart Gx) (hy : LocallyL2OnUpperChart Gy) :
    AEStronglyMeasurable (rawWeightedFiber Gx Gy) (volume : Measure UpperHalfPlane) := by
  have hvec : Continuous (fun p : ℂ×ℂ => (!₂[p.1,p.2] : GradientFiber)) := by
    apply PiLp.continuous_toLp.comp
    apply continuous_pi
    intro i
    fin_cases i
    · exact continuous_fst
    · exact continuous_snd
  exact ((Complex.continuous_ofReal.comp UpperHalfPlane.continuous_im).aestronglyMeasurable).smul
    (hvec.comp_aestronglyMeasurable ((locallyL2_chart_pullback_aestronglyMeasurable Gx hx).prodMk
      (locallyL2_chart_pullback_aestronglyMeasurable Gy hy)))

/-- Finite energy is only a finite nonnegative lintegral; global AE
measurability and integrability of the raw fibre are DERIVED. -/
theorem rawWeightedFiber_carrier_memLp (N : ℕ) [NeZero N] (Gx Gy : Plane → ℂ)
    (hx : LocallyL2OnUpperChart Gx) (hy : LocallyL2OnUpperChart Gy)
    (hfinite : (∫⁻ z,ENNReal.ofReal (rawCarrierEnergy Gx Gy z) ∂carrierVolume N)<∞) :
    MemLp (rawWeightedFiber Gx Gy) 2 (carrierVolume N) := by
  have hm : AEStronglyMeasurable (rawWeightedFiber Gx Gy) (carrierVolume N) :=
    (rawWeightedFiber_aestronglyMeasurable Gx Gy hx hy).mono_measure Measure.restrict_le_self
  apply (memLp_two_iff_integrable_sq_norm hm).2
  refine ⟨hm.norm.pow_const 2,?_⟩
  apply (hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun z => sq_nonneg
    ‖rawWeightedFiber Gx Gy z‖)).2
  simpa only [rawWeightedFiber_norm_sq] using hfinite

def rawWeightedFiberL2 (N : ℕ) [NeZero N] (Gx Gy : Plane → ℂ)
    (hx : LocallyL2OnUpperChart Gx) (hy : LocallyL2OnUpperChart Gy)
    (hfinite : (∫⁻ z,ENNReal.ofReal (rawCarrierEnergy Gx Gy z) ∂carrierVolume N)<∞) :
    CarrierGradientL2 N :=
  (rawWeightedFiber_carrier_memLp N Gx Gy hx hy hfinite).toLp (rawWeightedFiber Gx Gy)

theorem carrierGradientL2_norm_sq_integral (N : ℕ) [NeZero N] (u : CarrierGradientL2 N) :
    ‖u‖^2=∫ z,‖u z‖^2 ∂carrierVolume N := by
  apply Complex.ofRealLI.injective
  simpa [← LinearIsometry.integral_comp_comm,inner_self_eq_norm_sq_to_K] using
    (L2.inner_def (𝕜 := ℂ) u u)

theorem rawWeightedFiberL2_coe_ae (N : ℕ) [NeZero N] (Gx Gy : Plane → ℂ)
    (hx : LocallyL2OnUpperChart Gx) (hy : LocallyL2OnUpperChart Gy)
    (hfinite : (∫⁻ z,ENNReal.ofReal (rawCarrierEnergy Gx Gy z) ∂carrierVolume N)<∞) :
    rawWeightedFiberL2 N Gx Gy hx hy hfinite=ᵐ[carrierVolume N] rawWeightedFiber Gx Gy :=
  (rawWeightedFiber_carrier_memLp N Gx Gy hx hy hfinite).coeFn_toLp

theorem rawWeightedFiberL2_norm_sq (N : ℕ) [NeZero N] (Gx Gy : Plane → ℂ)
    (hx : LocallyL2OnUpperChart Gx) (hy : LocallyL2OnUpperChart Gy)
    (hfinite : (∫⁻ z,ENNReal.ofReal (rawCarrierEnergy Gx Gy z) ∂carrierVolume N)<∞) :
    ‖rawWeightedFiberL2 N Gx Gy hx hy hfinite‖^2=
      ∫ z,rawCarrierEnergy Gx Gy z ∂carrierVolume N := by
  have hn : (∫ z,‖rawWeightedFiberL2 N Gx Gy hx hy hfinite z‖^2 ∂carrierVolume N)=
      ‖rawWeightedFiberL2 N Gx Gy hx hy hfinite‖^2 := by
    apply Complex.ofRealLI.injective
    simpa [← LinearIsometry.integral_comp_comm,inner_self_eq_norm_sq_to_K] using
      (L2.inner_def (𝕜 := ℂ) (rawWeightedFiberL2 N Gx Gy hx hy hfinite)
        (rawWeightedFiberL2 N Gx Gy hx hy hfinite)).symm
  rw [← hn]
  apply integral_congr_ae
  filter_upwards [rawWeightedFiberL2_coe_ae N Gx Gy hx hy hfinite] with z hz
  rw [hz,rawWeightedFiber_norm_sq]

end
end ImbalancedChen.Part3.GammaRawWeightedFiberL220261026b
