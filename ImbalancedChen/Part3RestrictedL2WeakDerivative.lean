import ImbalancedChen.Part3GammaActualQuantitativeInteriorH1

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Restriction to ordinary local L2 is a contraction. The literal local
weak derivative relation is linear in its value and derivative classes,
and its derivative is UNIQUE on open sets by the native smooth-test
fundamental lemma. No derivative-linearity or continuity is assumed. -/

namespace ImbalancedChen.Part3.RestrictedL2WeakDerivative20261026b
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
open ProductConvolutionSecondDerivatives20261026a
open PlanarLocalWeakGradientExtraction20261026b

abbrev LocalL2 (Ω : Set Plane) := Lp ℂ 2 ((volume : Measure Plane).restrict Ω)

def restrictionLinear (Ω : Set Plane) : PlaneL2 →ₗ[ℂ] LocalL2 Ω where
  toFun f := (f.memLp.restrict Ω).toLp f
  map_add' f g := by
    apply Lp.ext
    filter_upwards [(f.memLp.restrict Ω).coeFn_toLp,(g.memLp.restrict Ω).coeFn_toLp,
      ((f+g).memLp.restrict Ω).coeFn_toLp,
      ae_restrict_of_ae (Lp.coeFn_add f g),
      Lp.coeFn_add ((f.memLp.restrict Ω).toLp f) ((g.memLp.restrict Ω).toLp g)] with p hf hg hfg hs ho
    rw [hfg,hs,ho,hf,hg]
    rfl
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [(f.memLp.restrict Ω).coeFn_toLp,((c • f).memLp.restrict Ω).coeFn_toLp,
      ae_restrict_of_ae (Lp.coeFn_smul c f),
      Lp.coeFn_smul c ((f.memLp.restrict Ω).toLp f)] with p hf hcf hs ho
    rw [hcf,hs,ho,hf]
    rfl

theorem restriction_norm_le (Ω : Set Plane) (f : PlaneL2) : ‖restrictionLinear Ω f‖≤‖f‖ := by
  rw [restrictionLinear,Lp.norm_toLp,Lp.norm_def]
  exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top f)
    (eLpNorm_mono_measure f Measure.restrict_le_self)

def restrictionCLM (Ω : Set Plane) : PlaneL2 →L[ℂ] LocalL2 Ω :=
  (restrictionLinear Ω).mkContinuous 1 (fun f => by simpa using restriction_norm_le Ω f)

theorem restriction_coe_ae (Ω : Set Plane) (f : PlaneL2) :
    (restrictionCLM Ω f : Plane → ℂ)=ᵐ[(volume : Measure Plane).restrict Ω] f :=
  (f.memLp.restrict Ω).coeFn_toLp

def testClass (Ω : Set Plane) {ψ : Plane → ℂ} (hψ : ContDiff ℝ ∞ ψ)
    (hc : HasCompactSupport ψ) : LocalL2 Ω :=
  ((hψ.continuous.memLp_of_hasCompactSupport hc).restrict Ω).toLp ψ

def derivativeTestClass (Ω : Set Plane) {ψ : Plane → ℂ} (hψ : ContDiff ℝ ∞ ψ)
    (hc : HasCompactSupport ψ) (v : Plane) : LocalL2 Ω :=
  (((directional_cinfty hψ v).continuous.memLp_of_hasCompactSupport
    (directional_hasCompactSupport hc v)).restrict Ω).toLp (directional v ψ)

theorem testClass_pair_integral (Ω : Set Plane) {ψ : Plane → ℂ}
    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ) (g : LocalL2 Ω) :
    inner ℂ (testClass Ω hψ hc) g =
      ∫ p,star (ψ p)*g p ∂(volume : Measure Plane).restrict Ω := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [((hψ.continuous.memLp_of_hasCompactSupport hc).restrict Ω).coeFn_toLp]
    with p hp
  rw [hp]
  simp only [RCLike.inner_apply',Complex.star_def]

def HasRestrictedDerivative (Ω : Set Plane) (f g : LocalL2 Ω) (v : Plane) : Prop :=
  ∀ (ψ : Plane → ℂ) (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ), tsupport ψ⊆Ω →
    inner ℂ (testClass Ω hψ hc) g = -inner ℂ (derivativeTestClass Ω hψ hc v) f

theorem restricted_derivative_add {Ω : Set Plane} {f g f' g' : LocalL2 Ω} {v : Plane}
    (h : HasRestrictedDerivative Ω f g v) (h' : HasRestrictedDerivative Ω f' g' v) :
    HasRestrictedDerivative Ω (f+f') (g+g') v := by
  intro ψ hψ hc hs
  rw [inner_add_right,h ψ hψ hc hs,h' ψ hψ hc hs,inner_add_right]
  ring

theorem restricted_derivative_smul {Ω : Set Plane} {f g : LocalL2 Ω} {v : Plane}
    (h : HasRestrictedDerivative Ω f g v) (c : ℂ) :
    HasRestrictedDerivative Ω (c • f) (c • g) v := by
  intro ψ hψ hc hs
  rw [inner_smul_right,inner_smul_right,h ψ hψ hc hs]
  ring

theorem restricted_derivative_of_global_tests {Ω : Set Plane} (hΩ : MeasurableSet Ω)
    (F : Plane → ℂ) (f : LocalL2 Ω) (hfeq : f=ᵐ[(volume : Measure Plane).restrict Ω] F)
    (g : PlaneL2) (v : Plane)
    (hw : ∀ ψ : Plane → ℂ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ⊆Ω →
      (∫ p,star (ψ p)*g p)=-(∫ p,star (directional v ψ p)*F p)) :
    HasRestrictedDerivative Ω f (restrictionCLM Ω g) v := by
  intro ψ hψ hc hs
  have hleft : inner ℂ (testClass Ω hψ hc) (restrictionCLM Ω g)=
      ∫ p,star (ψ p)*g p := by
    rw [testClass_pair_integral]
    calc
      _ = ∫ p,star (ψ p)*g p ∂(volume : Measure Plane).restrict Ω := by
        apply integral_congr_ae
        filter_upwards [restriction_coe_ae Ω g] with p hp
        rw [hp]
      _ = _ := setIntegral_eq_integral_of_forall_compl_eq_zero (fun p hp => by
        have hz : ψ p=0 := image_eq_zero_of_notMem_tsupport (fun hpin => hp (hs hpin))
        rw [hz,star_zero,zero_mul])
  have hright : inner ℂ (derivativeTestClass Ω hψ hc v) f=
      ∫ p,star (directional v ψ p)*F p := by
    have he : derivativeTestClass Ω hψ hc v=
        testClass Ω (directional_cinfty hψ v) (directional_hasCompactSupport hc v) := rfl
    rw [he,testClass_pair_integral]
    calc
      _ = ∫ p,star (directional v ψ p)*F p ∂(volume : Measure Plane).restrict Ω := by
        apply integral_congr_ae
        filter_upwards [hfeq] with p hp
        rw [hp]
      _ = _ := setIntegral_eq_integral_of_forall_compl_eq_zero (fun p hp => by
        have hn : p∉tsupport ψ := fun hpin => hp (hs hpin)
        unfold directional
        rw [fderiv_of_notMem_tsupport hn]
        simp)
  rw [hleft,hright]
  exact hw ψ hψ hc hs

theorem restricted_derivative_unique {Ω : Set Plane} (hΩ : IsOpen Ω)
    {f g h : LocalL2 Ω} {v : Plane}
    (hg : HasRestrictedDerivative Ω f g v) (hh : HasRestrictedDerivative Ω f h v) : g=h := by
  have hl : LocallyIntegrableOn (fun p => g p-h p) Ω volume :=
    locallyIntegrableOn_of_locallyIntegrable_restrict
      ((g.memLp.locallyIntegrable (by norm_num)).sub (h.memLp.locallyIntegrable (by norm_num)))
  have hz : ∀ᵐ p ∂(volume : Measure Plane),p∈Ω → g p-h p=0 := by
    apply hΩ.ae_eq_zero_of_integral_contDiff_smul_eq_zero hl
    intro φ hφ hφc hφs
    let ψ : Plane → ℂ := fun p => (φ p : ℂ)
    have hψ : ContDiff ℝ ∞ ψ := Complex.ofRealCLM.contDiff.comp hφ
    have hψc : HasCompactSupport ψ := hφc.comp_left (g := Complex.ofReal) rfl
    have hψs : tsupport ψ⊆Ω := (tsupport_comp_subset (g := Complex.ofReal) rfl φ).trans hφs
    have he : (∫ p,φ p • g p ∂(volume : Measure Plane).restrict Ω)=
        ∫ p,φ p • h p ∂(volume : Measure Plane).restrict Ω := by
      have hp := (hg ψ hψ hψc hψs).trans (hh ψ hψ hψc hψs).symm
      rw [testClass_pair_integral,testClass_pair_integral] at hp
      simpa only [ψ,Complex.star_def,Complex.conj_ofReal,Complex.real_smul] using hp
    have hig : Integrable (fun p => φ p • g p) ((volume : Measure Plane).restrict Ω) :=
      (g.memLp.locallyIntegrable (by norm_num)).integrable_smul_left_of_hasCompactSupport hφ.continuous hφc
    have hih : Integrable (fun p => φ p • h p) ((volume : Measure Plane).restrict Ω) :=
      (h.memLp.locallyIntegrable (by norm_num)).integrable_smul_left_of_hasCompactSupport hφ.continuous hφc
    have hlocal : (∫ p,φ p • (g p-h p) ∂(volume : Measure Plane).restrict Ω)=0 := by
      simp only [smul_sub]
      rw [integral_sub hig hih,he,sub_self]
    rw [← hlocal]
    exact (setIntegral_eq_integral_of_forall_compl_eq_zero (fun p hp => by
      have hφzero : φ p=0 := image_eq_zero_of_notMem_tsupport (fun hpin => hp (hφs hpin))
      rw [hφzero,zero_smul])).symm
  apply Lp.ext
  apply (ae_restrict_iff' hΩ.measurableSet).2
  filter_upwards [hz] with p hp
  exact fun hpin => sub_eq_zero.mp (hp hpin)

end
end ImbalancedChen.Part3.RestrictedL2WeakDerivative20261026b
