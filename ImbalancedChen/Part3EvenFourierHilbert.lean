import ImbalancedChen.Part3HalfCosinePlancherel

/-!
SOURCEONLY / UNCOMPILED, 2026-10-24.
The primitive cosine Hilbert space is the reflection-fixed closed
subspace of complex L2(R). Fourier and inverse Fourier preserve this
space, and their restrictions form a genuine linear isometry equivalence.
The commutation proof starts with actual integral Fourier transforms on
L1 ∩ L2 and extends by Schwartz density. No unitary property is assumed.
-/

noncomputable section

namespace ImbalancedChen.Part3.EvenFourierHilbertSourceOnly

open MeasureTheory SchwartzMap FourierTransform
open scoped FourierTransform SchwartzMap
open FourierL1L2PlancherelSourceOnly HalfCosinePlancherelSourceOnly
open KFullLineFourierBridgeSourceOnly P3ActualKProfileLpSourceOnly
open ImaginaryOrderKBesselSourceOnly

abbrev ComplexL2 := Lp (α := ℝ) ℂ 2 volume

private theorem neg_measurePreserving :
    MeasurePreserving (fun x : ℝ => -x) volume volume := by
  exact (LinearIsometryEquiv.neg ℝ : ℝ ≃ₗᵢ[ℝ] ℝ).measurePreserving

/-- Reflection is a complex-linear isometry on the actual quotient L2. -/
def reflection : ComplexL2 →ₗᵢ[ℂ] ComplexL2 :=
  Lp.compMeasurePreservingₗᵢ ℂ (fun x : ℝ => -x) neg_measurePreserving

theorem reflection_coe (f : ComplexL2) :
    (reflection f : ℝ → ℂ) =ᵐ[volume] fun x : ℝ => f (-x) := by
  exact Lp.coeFn_compMeasurePreserving f neg_measurePreserving

theorem reflection_involutive (f : ComplexL2) :
    reflection (reflection f) = f := by
  apply Lp.ext
  filter_upwards [reflection_coe (reflection f),
    neg_measurePreserving.quasiMeasurePreserving.ae_eq (reflection_coe f)]
    with x hx hnx
  simpa only [Function.comp_apply, neg_neg] using hx.trans hnx

theorem reflection_toLp {f : ℝ → ℂ} (hf : MemLp f 2) :
    reflection (hf.toLp f) =
      (hf.comp_measurePreserving neg_measurePreserving).toLp
        (fun x : ℝ => f (-x)) := by
  exact Lp.toLp_compMeasurePreserving hf neg_measurePreserving

/-- Integral-Fourier commutation with reflection on L1 ∩ L2. -/
theorem reflection_fourier_toLp {f : ℝ → ℂ}
    (hf₁ : Integrable f) (hf₂ : MemLp f 2) :
    reflection (𝓕 (hf₂.toLp f)) = 𝓕 (reflection (hf₂.toLp f)) := by
  rw [reflection_toLp]
  apply Lp.ext
  have hleft := (reflection_coe (𝓕 (hf₂.toLp f))).trans
    (neg_measurePreserving.quasiMeasurePreserving.ae_eq
      (fourier_toLp_ae_eq hf₁ hf₂))
  have hright := fourier_toLp_ae_eq hf₁.comp_neg
    (hf₂.comp_measurePreserving neg_measurePreserving)
  filter_upwards [hleft, hright] with x hx hy
  calc
    _ = 𝓕 f (-x) := hx
    _ = 𝓕 (fun u : ℝ => f (-u)) x := by
      simpa only [LinearIsometryEquiv.coe_neg, Function.comp_apply] using
        (Real.fourier_comp_linearIsometry
          (LinearIsometryEquiv.neg ℝ : ℝ ≃ₗᵢ[ℝ] ℝ) f x).symm
    _ = _ := hy.symm

/-- Commutation on all L2 follows by the actual dense Schwartz embedding. -/
theorem reflection_fourier (f : ComplexL2) :
    reflection (𝓕 f) = 𝓕 (reflection f) := by
  let p := fun g : ComplexL2 => reflection (𝓕 g) = 𝓕 (reflection g)
  apply DenseRange.induction_on (p := p)
    (SchwartzMap.denseRange_toLpCLM (E := ℝ) (F := ℂ) (p := 2)
      ENNReal.ofNat_ne_top) f
  · exact isClosed_eq
      (reflection.continuous.comp (Lp.fourierTransformₗᵢ ℝ ℂ).continuous)
      ((Lp.fourierTransformₗᵢ ℝ ℂ).continuous.comp reflection.continuous)
  · intro g
    exact reflection_fourier_toLp g.integrable (g.memLp 2)

theorem reflection_fourierInv (f : ComplexL2) :
    reflection (𝓕⁻ f) = 𝓕⁻ (reflection f) := by
  apply (Lp.fourierTransformₗᵢ ℝ ℂ).injective
  change 𝓕 (reflection (𝓕⁻ f)) = 𝓕 (𝓕⁻ (reflection f))
  rw [← reflection_fourier, fourier_fourierInv_eq, fourier_fourierInv_eq]

/-- The primitive even Hilbert subspace, defined on genuine L2 classes. -/
def evenL2 : Submodule ℂ ComplexL2 where
  carrier := {f | reflection f = f}
  zero_mem' := map_zero reflection
  add_mem' := by
    intro f g hf hg
    change reflection (f + g) = f + g
    rw [map_add, hf, hg]
  smul_mem' := by
    intro c f hf
    change reflection (c • f) = c • f
    rw [map_smul, hf]

theorem mem_evenL2_iff (f : ComplexL2) :
    f ∈ evenL2 ↔ reflection f = f := by rfl

theorem mem_evenL2_iff_ae (f : ComplexL2) :
    f ∈ evenL2 ↔ (fun x : ℝ => f (-x)) =ᵐ[volume] f := by
  constructor
  · intro hf
    have h := reflection_coe f
    rw [(mem_evenL2_iff f).1 hf] at h
    exact h.symm
  · intro hf
    exact Lp.ext ((reflection_coe f).trans hf)

theorem isClosed_evenL2 : IsClosed (evenL2 : Set ComplexL2) := by
  exact isClosed_eq reflection.continuous continuous_id

instance : CompleteSpace evenL2 := isClosed_evenL2.isComplete.completeSpace_coe

theorem fourier_mem_evenL2 {f : ComplexL2} (hf : f ∈ evenL2) :
    𝓕 f ∈ evenL2 := by
  change reflection (𝓕 f) = 𝓕 f
  rw [reflection_fourier, (mem_evenL2_iff f).1 hf]

theorem fourierInv_mem_evenL2 {f : ComplexL2} (hf : f ∈ evenL2) :
    𝓕⁻ f ∈ evenL2 := by
  change reflection (𝓕⁻ f) = 𝓕⁻ f
  rw [reflection_fourierInv, (mem_evenL2_iff f).1 hf]

/-- Fourier restricted to the closed even Hilbert space; the inverse is
the restriction of Mathlib's actual inverse Fourier transform. -/
def evenFourier : evenL2 ≃ₗᵢ[ℂ] evenL2 where
  toFun f := ⟨𝓕 (f : ComplexL2), fourier_mem_evenL2 f.property⟩
  invFun f := ⟨𝓕⁻ (f : ComplexL2), fourierInv_mem_evenL2 f.property⟩
  left_inv f := by
    apply Subtype.ext
    exact fourierInv_fourier_eq (f : ComplexL2)
  right_inv f := by
    apply Subtype.ext
    exact fourier_fourierInv_eq (f : ComplexL2)
  map_add' f g := by
    apply Subtype.ext
    exact (Lp.fourierTransformₗᵢ ℝ ℂ).map_add (f : ComplexL2) (g : ComplexL2)
  map_smul' c f := by
    apply Subtype.ext
    exact (Lp.fourierTransformₗᵢ ℝ ℂ).map_smul c (f : ComplexL2)
  norm_map' f := Lp.norm_fourier_eq (f : ComplexL2)

theorem evenFourier_coe (f : evenL2) :
    (evenFourier f : ComplexL2) = 𝓕 (f : ComplexL2) := by rfl

theorem evenFourier_symm_coe (f : evenL2) :
    (evenFourier.symm f : ComplexL2) = 𝓕⁻ (f : ComplexL2) := by rfl

theorem evenFourier_norm (f : evenL2) : ‖evenFourier f‖ = ‖f‖ := by
  exact evenFourier.norm_map f

/-- Any actual even square-integrable function defines a member of the
closed subspace, independently of its chosen a.e. representative. -/
theorem toLp_mem_evenL2 {f : ℝ → ℂ} (hf : MemLp f 2)
    (heven : ∀ x : ℝ, f (-x) = f x) : hf.toLp f ∈ evenL2 := by
  apply (mem_evenL2_iff_ae _).2
  filter_upwards [hf.coeFn_toLp,
    neg_measurePreserving.quasiMeasurePreserving.ae_eq hf.coeFn_toLp]
    with x hx hnx
  change hf.toLp f (-x) = hf.toLp f x
  change hf.toLp f (-x) = f (-x) at hnx
  rw [hnx, heven, hx]

/-- The actual q-profile as an element of the primitive cosine Hilbert space. -/
def evenKProfile (q : ℝ) (hq : 0 < q) : evenL2 :=
  ⟨(kEvenProfile_memLp_two hq).toLp (kEvenProfile q),
    toLp_mem_evenL2 (kEvenProfile_memLp_two hq) (kEvenProfile_neg q)⟩

/-- Actual identification of its Fourier image with the K-height curve,
including the frequency pi and amplitude two. -/
theorem evenFourier_evenKProfile_ae (q : ℝ) (hq : 0 < q) :
    ((evenFourier (evenKProfile q hq) : ComplexL2) : ℝ → ℂ) =ᵐ[volume]
      fun ξ : ℝ => (2 : ℂ) * (imaginaryOrderK (Real.pi * ξ) q : ℂ) := by
  exact (fourier_toLp_ae_eq (kEvenProfile_integrable hq)
    (kEvenProfile_memLp_two hq)).trans
      (Filter.Eventually.of_forall (fun ξ => fourier_kEvenProfile_eq q ξ hq))

theorem imaginaryOrderK_complex_continuous {q : ℝ} (hq : 0 < q) :
    Continuous (fun t : ℝ => (imaginaryOrderK t q : ℂ)) := by
  have hF : Continuous (𝓕 (kEvenProfile q)) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ (kEvenProfile_integrable hq)
  have hscaled : Continuous (fun t : ℝ =>
      (1 / 2 : ℂ) * 𝓕 (kEvenProfile q) (t / Real.pi)) := by
    exact continuous_const.mul (hF.comp (by fun_prop))
  have heq : (fun t : ℝ => (imaginaryOrderK t q : ℂ)) =
      (fun t : ℝ => (1 / 2 : ℂ) * 𝓕 (kEvenProfile q) (t / Real.pi)) :=
    funext (fun t => imaginaryOrderK_eq_half_fourier t q hq)
  rw [heq]
  exact hscaled

theorem imaginaryOrderK_complex_memLp_two {q : ℝ} (hq : 0 < q) :
    MemLp (fun t : ℝ => (imaginaryOrderK t q : ℂ)) 2 := by
  apply (memLp_two_iff_integrable_sq_norm
    (imaginaryOrderK_complex_continuous hq).aestronglyMeasurable).2
  simpa only [Complex.norm_real, Real.norm_eq_abs] using
    imaginaryOrderK_sq_integrable hq

/-- The actual unscaled K-height curve belongs to the same closed even space. -/
def evenKHeight (q : ℝ) (hq : 0 < q) : evenL2 :=
  ⟨(imaginaryOrderK_complex_memLp_two hq).toLp
      (fun t : ℝ => (imaginaryOrderK t q : ℂ)),
    toLp_mem_evenL2 (imaginaryOrderK_complex_memLp_two hq)
      (fun t => by rw [imaginaryOrderK_neg])⟩

theorem evenKHeight_coe_ae (q : ℝ) (hq : 0 < q) :
    ((evenKHeight q hq : ComplexL2) : ℝ → ℂ) =ᵐ[volume]
      fun t : ℝ => (imaginaryOrderK t q : ℂ) := by
  exact (imaginaryOrderK_complex_memLp_two hq).coeFn_toLp

end ImbalancedChen.Part3.EvenFourierHilbertSourceOnly
