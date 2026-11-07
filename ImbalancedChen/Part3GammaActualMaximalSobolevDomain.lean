import ImbalancedChen.Part3GammaRawH1CutoffFormDomain
import ImbalancedChen.Part3GammaActualGlobalWeakGradientEnergy
import ImbalancedChen.Part3GammaActualClosedGradientRealization
import ImbalancedChen.Part3GammaRawQuotientCutoffH1
import ImbalancedChen.Part3GammaRawLeibnizCarrierConvergence
import ImbalancedChen.Part3GammaActualCutoffOperatorGraphConvergence
import ImbalancedChen.Part3GammaRawCutoffDerivativeFiberIdentity

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
The original actual closed-form domain is characterized by raw whole-H
weak H1 regularity and finite literal carrier energy. The converse
constructs ACTUAL cutoff form vectors, derives their gradients from the
proved raw Leibniz tests, proves both native L2 limits, and reconstructs
the original energy vector through the actual closed gradient graph.
No form membership, desired gradient limit, graph density or cutoff
approximation premise is supplied.
-/

namespace ImbalancedChen.Part3.GammaActualMaximalSobolevDomain20261026b
noncomputable section
open Set Filter MeasureTheory
open Gamma0ActualSmoothQuotientCore20261025a Gamma0ActualEnergyCompletion20261025a
open Gamma0ActualFriedrichsOperator20261025a Gamma0CarrierGradientHilbertMap20261026b
open GammaActualClosedGradientRealization20261026b
open ProductConvolutionSecondDerivatives20261026a
open ActualPullbackLocalH1Transfer20261026b WholeUpperChartWeakH1Patching20261026b
open GammaActualGlobalWeakGradientEnergy20261026b
open CanonicalTensorHyperbolicLaplacianForm20261024z
open Gamma0QuotientCellPushforward20261025a GammaRawH1CutoffFormDomain20261026b
open GammaActualQuotientCutoffMultiplier20261026b GammaSmoothMultiplierLegalTests20261026a
open ActualModularSmoothCutoffL2Tail20261025a Gamma0WeightedCutoffDefectLimit20261026a
open GammaRawQuotientCutoffH120261026b GammaRawWeightedFiberL220261026b
open GammaRawCutoffLeibnizFiber20261026b GammaRawLeibnizCarrierConvergence20261026b
open GammaActualCutoffOperatorGraphConvergence20261026b
open GammaRawCutoffDerivativeFiberIdentity20261026b

/-- Literal maximal finite-energy Sobolev condition on the ORIGINAL
quotient Hilbert space. Gradient components are functions on the whole
chart, locally ordinary L2; only their energy is integrated on carrier H.
No form-domain or native operator-domain predicate occurs in this definition. -/
def HasFiniteCarrierWeakH1 (N : ℕ) [NeZero N] (f : QuotientL2 N) : Prop :=
  ∃ Gx Gy : Plane → ℂ,
    (∀ K : Set Plane, IsCompact K → K ⊆ upperChart →
      MemLp (actualPlanePullback N f) 2 (volume.restrict K) ∧
      MemLp Gx 2 (volume.restrict K) ∧ MemLp Gy 2 (volume.restrict K)) ∧
    (∀ ψ : Plane → ℂ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ upperChart →
      ((∫ p, star (ψ p)*Gx p) = -(∫ p,
        star (directional xDirection ψ p)*actualPlanePullback N f p)) ∧
      ((∫ p, star (ψ p)*Gy p) = -(∫ p,
        star (directional yDirection ψ p)*actualPlanePullback N f p))) ∧
    Integrable (globalRawGradientEnergy Gx Gy) (carrierVolume N)

theorem actual_form_has_finite_carrier_weakH1 (N : ℕ) [NeZero N]
    (f : QuotientL2 N) (hf : f ∈ actualEnergyFormDomain N) :
    HasFiniteCarrierWeakH1 N f := by
  let u : actualEnergyFormDomain N := ⟨f,hf⟩
  obtain ⟨Gx,Gy,hloc,hw,hi,heq⟩ :=
    completed_has_global_raw_gradient_energy N (actualEnergyLift N u)
  refine ⟨Gx,Gy,?_,?_,hi⟩
  · simpa only [actualEnergyLift_projection] using hloc
  · simpa only [actualEnergyLift_projection] using hw

private theorem quotient_cutoff_product_ae (N : ℕ) [NeZero N]
    (Y : ℝ) (hY : 1 < Y) (f : QuotientL2 N) :
    (actualQuotientCutoffMultiplier N Y hY f : Gamma0OrbitSpace N → ℂ)
      =ᵐ[carrierPushforward N] fun q => (quotientCutoff N Y q : ℂ)*f q := by
  simpa only [actualCutoff_quotientMultiplier,Pi.mul_apply] using
    actualQuotientCutoffMultiplier_coe_ae N Y hY f

/-- An explicitly constructed point of the EXISTING form domain, before
any global finite-energy hypothesis on the raw quotient vector is used. -/
def rawSobolevCutoffFormPoint (N : ℕ) [NeZero N] (f : QuotientL2 N)
    (hraw : HasUpperChartWeakH1 (actualPlanePullback N f)) (n : ℕ) :
    actualEnergyFormDomain N :=
  ⟨actualQuotientCutoffMultiplier N (cutoffHeight n) (cutoffHeight_gt_one n) f,
    raw_H1_cutoff_mem_form_domain N f hraw (cutoffHeight n) (cutoffHeight_gt_one n).le _
      (quotient_cutoff_product_ae N (cutoffHeight n) (cutoffHeight_gt_one n) f)⟩

def rawSobolevCutoffEnergyVector (N : ℕ) [NeZero N] (f : QuotientL2 N)
    (hraw : HasUpperChartWeakH1 (actualPlanePullback N f)) (n : ℕ) : EnergyCompletion N :=
  actualEnergyLift N (rawSobolevCutoffFormPoint N f hraw n)

theorem rawSobolevCutoffEnergyVector_projection (N : ℕ) [NeZero N] (f : QuotientL2 N)
    (hraw : HasUpperChartWeakH1 (actualPlanePullback N f)) (n : ℕ) :
    physicalProjection N (rawSobolevCutoffEnergyVector N f hraw n) =
      actualQuotientCutoffMultiplier N (cutoffHeight n) (cutoffHeight_gt_one n) f :=
  actualEnergyLift_projection N _

/-- Independent physical and carrier-gradient limits reconstruct an
actual energy vector, and imply STRONG energy convergence. The latter
is derived from the actual graph inverse estimate, not assumed. -/
theorem energy_reconstruction_of_value_gradient_limits (N : ℕ) [NeZero N]
    (e : ℕ → EnergyCompletion N) (f : QuotientL2 N) (g : CarrierGradientL2 N)
    (hf : Tendsto (fun n => physicalProjection N (e n)) atTop (𝓝 f))
    (hg : Tendsto (fun n => completedCarrierGradient N (e n)) atTop (𝓝 g)) :
    ∃ v : EnergyCompletion N, physicalProjection N v = f ∧
      completedCarrierGradient N v = g ∧ Tendsto e atTop (𝓝 v) := by
  have hp : Tendsto (fun n => gradientGraphEmbedding N (e n)) atTop (𝓝 (f,g)) :=
    hf.prodMk_nhds hg
  have hmem : (f,g) ∈ Set.range (gradientGraphEmbedding N) :=
    (gradientGraphEmbedding_closed_range N).mem_of_tendsto hp
      (Eventually.of_forall (fun n => ⟨e n,rfl⟩))
  obtain ⟨v,hv⟩ := hmem
  have hvf : physicalProjection N v = f := congrArg Prod.fst hv
  have hvg : completedCarrierGradient N v = g := congrArg Prod.snd hv
  have hb (n : ℕ) : ‖e n-v‖ ≤
      ‖physicalProjection N (e n)-f‖ + ‖completedCarrierGradient N (e n)-g‖ := by
    have h := energy_norm_le_value_add_gradient N (e n-v)
    simpa only [map_sub,hvf,hvg] using h
  have hzero : Tendsto (fun n => ‖e n-v‖) atTop (𝓝 0) := by
    apply squeeze_zero (fun n => norm_nonneg _) hb
    simpa only [sub_self,norm_zero,zero_add] using
      ((hf.sub tendsto_const_nhds).norm.add (hg.sub tendsto_const_nhds).norm)
  refine ⟨v,hvf,hvg,?_⟩
  exact tendsto_iff_norm_sub_tendsto_zero.mpr hzero

/-- Genuine maximal Sobolev converse. The cutoff form vectors and BOTH
native limits are constructed; neither form membership nor a claimed
gradient limit is a premise. No scalar coordinate-gradient descent is used. -/
theorem finite_carrier_weakH1_mem_actual_form_domain (N : ℕ) [NeZero N]
    (f : QuotientL2 N) (hf : HasFiniteCarrierWeakH1 N f) :
    f ∈ actualEnergyFormDomain N := by
  obtain ⟨Gx,Gy,hb,hw,hi⟩ := hf
  have hraw : HasUpperChartWeakH1 (actualPlanePullback N f) := ⟨Gx,Gy,hb,hw⟩
  have hx : LocallyL2OnUpperChart Gx := fun K hK hs => (hb K hK hs).2.1
  have hy : LocallyL2OnUpperChart Gy := fun K hK hs => (hb K hK hs).2.2
  have hi' : Integrable (rawCarrierEnergy Gx Gy) (carrierVolume N) := hi
  have hn : ∀ᵐ z ∂carrierVolume N, 0 ≤ rawCarrierEnergy Gx Gy z :=
    Eventually.of_forall (fun z => mul_nonneg (sq_nonneg _)
      (add_nonneg (sq_nonneg _) (sq_nonneg _)))
  have hfinite : (∫⁻ z, ENNReal.ofReal (rawCarrierEnergy Gx Gy z) ∂carrierVolume N) < ∞ :=
    (hasFiniteIntegral_iff_ofReal hn).mp hi'.hasFiniteIntegral
  let hW := rawWeightedFiber_carrier_memLp N Gx Gy hx hy hfinite
  let e := rawSobolevCutoffEnergyVector N f hraw
  have hJe (n : ℕ) : physicalProjection N (e n) =
      actualQuotientCutoffMultiplier N (cutoffHeight n) (cutoffHeight_gt_one n) f :=
    rawSobolevCutoffEnergyVector_projection N f hraw n
  have hGe (n : ℕ) : completedCarrierGradient N (e n) = rawLeibnizFiberL2 N f hW n := by
    let X := rawCutoffDx (cutoffHeight n) (actualPlanePullback N f) Gx
    let Y := rawCutoffDy (cutoffHeight n) (actualPlanePullback N f) Gy
    obtain ⟨hbY,hwY⟩ := actual_quotient_cutoff_raw_H1_packet N f Gx Gy hb hw
      (cutoffHeight n) (cutoffHeight_gt_one n)
    have hident := completed_global_raw_gradient_identification N (e n) X Y
      (by simpa only [hJe n] using hbY)
      (by simpa only [hJe n] using hwY)
    apply Lp.ext
    filter_upwards [hident,(rawLeibnizFiber_memLp N f hW n).coeFn_toLp] with z hz hclass
    change rawLeibnizFiberL2 N f hW n z = rawLeibnizFiber N f (rawWeightedFiber Gx Gy) n z at hclass
    rw [hclass,← raw_cutoff_weighted_fiber_eq_Leibniz N f Gx Gy n]
    ext i
    fin_cases i
    · simpa only [rawWeightedFiber,PiLp.smul_apply,PiLp.toLp_apply,Matrix.cons_val_zero,
        smul_eq_mul] using hz.1
    · simpa only [rawWeightedFiber,PiLp.smul_apply,PiLp.toLp_apply,Matrix.cons_val_one,
        smul_eq_mul] using hz.2
  have hJlim : Tendsto (fun n => physicalProjection N (e n)) atTop (𝓝 f) := by
    simp_rw [hJe]
    exact actualQuotientCutoffMultiplier_tendsto N f
  have hGlim : Tendsto (fun n => completedCarrierGradient N (e n)) atTop
      (𝓝 (hW.toLp (rawWeightedFiber Gx Gy))) := by
    simp_rw [hGe]
    exact rawLeibnizFiberL2_strong N f hW
  obtain ⟨v,hvf,hvg,hev⟩ := energy_reconstruction_of_value_gradient_limits N e f
    (hW.toLp (rawWeightedFiber Gx Gy)) hJlim hGlim
  exact ⟨v,hvf⟩

/-- Exact identification with the SAME original actual closed-form
domain, rather than an auxiliary plane or cylinder Sobolev space. -/
theorem actual_form_domain_iff_finite_carrier_weakH1 (N : ℕ) [NeZero N]
    (f : QuotientL2 N) :
    f ∈ actualEnergyFormDomain N ↔ HasFiniteCarrierWeakH1 N f :=
  ⟨actual_form_has_finite_carrier_weakH1 N f,
    finite_carrier_weakH1_mem_actual_form_domain N f⟩

end
end ImbalancedChen.Part3.GammaActualMaximalSobolevDomain20261026b
