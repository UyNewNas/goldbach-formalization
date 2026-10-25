import ImbalancedChen.Part3HalfCosineL2Extension
import ImbalancedChen.Part3ActualKProfileTotality

/-!
CODE_ONLY / SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED, 2026-10-25.
The raw half-cosine map has even codomain, is onto actual evenL2, and keeps
the literal norm-squared factor pi/4. Transport of spatial profile totality
proves totality of the actual raw-height functions t -> K_{2it}(q).
These use Lebesgue dt; no Kontorovich-Lebedev measure is introduced.
-/

noncomputable section

namespace ImbalancedChen.Part3.ActualKHeightTotalitySourceOnly

open Set MeasureTheory FourierTransform
open scoped FourierTransform
open EvenFourierHilbertSourceOnly EvenL1L2DensitySourceOnly
open HalfCosinePlancherelSourceOnly HalfCosineL2ExtensionSourceOnly
open ActualKWeightedPolynomialClosureSourceOnly ActualKProfileTotalitySourceOnly
open KFullLineFourierBridgeSourceOnly ImaginaryOrderKBesselSourceOnly

private theorem negPreserving :
    MeasurePreserving (fun t : ℝ => -t) volume volume := by
  exact (LinearIsometryEquiv.neg ℝ : ℝ ≃ₗᵢ[ℝ] ℝ).measurePreserving

private theorem divPi_quasiMeasurePreserving :
    QuasiMeasurePreserving (fun t : ℝ => t / Real.pi) volume volume := by
  simpa only [smul_eq_mul, div_eq_mul_inv, mul_comm] using
    (Measure.quasiMeasurePreserving_smul (volume : Measure ℝ)
      (inv_ne_zero Real.pi_ne_zero))

private theorem mulPi_quasiMeasurePreserving :
    QuasiMeasurePreserving (fun t : ℝ => Real.pi * t) volume volume := by
  simpa only [smul_eq_mul] using
    (Measure.quasiMeasurePreserving_smul (volume : Measure ℝ) Real.pi_ne_zero)

private theorem inverseDilation_memLp (f : ComplexL2) :
    MemLp (fun t : ℝ => f (Real.pi * t)) 2 := by
  have hm := (Lp.memLp f).aestronglyMeasurable.comp_quasiMeasurePreserving
    mulPi_quasiMeasurePreserving
  apply (memLp_two_iff_integrable_sq_norm hm).2
  exact ((memLp_two_iff_integrable_sq_norm
    (Lp.memLp f).aestronglyMeasurable).1 (Lp.memLp f)).comp_mul_left'
      Real.pi_ne_zero

/-- The genuine inverse quotient dilation, with literal argument pi*t. -/
def inverseDilation (f : ComplexL2) : ComplexL2 :=
  (inverseDilation_memLp f).toLp (fun t : ℝ => f (Real.pi * t))

theorem inverseDilation_coe (f : ComplexL2) :
    (inverseDilation f : ℝ → ℂ) =ᵐ[volume] fun t : ℝ => f (Real.pi * t) :=
  (inverseDilation_memLp f).coeFn_toLp

theorem dilation_inverseDilation (f : ComplexL2) :
    dilation (inverseDilation f) = f := by
  apply Lp.ext
  filter_upwards [dilation_coe (inverseDilation f),
    divPi_quasiMeasurePreserving.ae_eq (inverseDilation_coe f)] with t ht hs
  change inverseDilation f (t / Real.pi) = f (Real.pi * (t / Real.pi)) at hs
  have harg : Real.pi * (t / Real.pi) = t := by field_simp [Real.pi_ne_zero]
  exact ht.trans (by simpa only [harg] using hs)

theorem inverseDilation_dilation (f : ComplexL2) :
    inverseDilation (dilation f) = f := by
  apply Lp.ext
  filter_upwards [inverseDilation_coe (dilation f),
    mulPi_quasiMeasurePreserving.ae_eq (dilation_coe f)] with t ht hs
  change dilation f (Real.pi * t) = f ((Real.pi * t) / Real.pi) at hs
  have harg : (Real.pi * t) / Real.pi = t := by field_simp [Real.pi_ne_zero]
  exact ht.trans (by simpa only [harg] using hs)

/-- The frequency dilation preserves actual a.e. evenness. -/
theorem dilation_mem_evenL2 {f : ComplexL2} (hf : f ∈ evenL2) :
    dilation f ∈ evenL2 := by
  apply (mem_evenL2_iff_ae _).2
  have hpar := divPi_quasiMeasurePreserving.ae_eq ((mem_evenL2_iff_ae f).1 hf)
  filter_upwards [dilation_coe f,
    negPreserving.quasiMeasurePreserving.ae_eq (dilation_coe f), hpar]
    with t ht hn hp
  change dilation f (-t) = dilation f t
  change dilation f (-t) = f ((-t) / Real.pi) at hn
  change f (-(t / Real.pi)) = f (t / Real.pi) at hp
  rw [hn, neg_div, hp, ht]

theorem inverseDilation_mem_evenL2 {f : ComplexL2} (hf : f ∈ evenL2) :
    inverseDilation f ∈ evenL2 := by
  apply (mem_evenL2_iff_ae _).2
  have hpar := mulPi_quasiMeasurePreserving.ae_eq ((mem_evenL2_iff_ae f).1 hf)
  filter_upwards [inverseDilation_coe f,
    negPreserving.quasiMeasurePreserving.ae_eq (inverseDilation_coe f), hpar]
    with t ht hn hp
  change inverseDilation f (-t) = inverseDilation f t
  change inverseDilation f (-t) = f (Real.pi * (-t)) at hn
  change f (-(Real.pi * t)) = f (Real.pi * t) at hp
  rw [hn, mul_neg, hp, ht]

/-- The actual dilation restricted to even classes, with an explicit onto proof. -/
def evenDilation : evenL2 →L[ℂ] evenL2 :=
  (dilationCLM.comp evenL2.subtypeL).codRestrict evenL2
    (fun f => dilation_mem_evenL2 f.property)

theorem evenDilation_surjective : Function.Surjective evenDilation := by
  intro f
  refine ⟨⟨inverseDilation (f : ComplexL2), inverseDilation_mem_evenL2 f.property⟩, ?_⟩
  apply Subtype.ext
  exact dilation_inverseDilation (f : ComplexL2)

theorem rawHalfCosine_mem_evenL2 (f : evenL2) : rawHalfCosine f ∈ evenL2 := by
  rw [rawHalfCosine_apply]
  exact evenL2.smul_mem (1 / 2 : ℂ) (dilation_mem_evenL2 (evenFourier f).property)

/-- The bounded raw half-cosine operator with its actual even codomain. -/
def rawHalfCosineEven : evenL2 →L[ℂ] evenL2 :=
  rawHalfCosine.codRestrict evenL2 rawHalfCosine_mem_evenL2

/-- No isometry normalization is hidden: the squared-norm coefficient is pi/4. -/
theorem rawHalfCosineEven_norm_sq (f : evenL2) :
    ‖rawHalfCosineEven f‖ ^ 2 = (Real.pi / 4) * ‖f‖ ^ 2 :=
  rawHalfCosine_norm_sq f

theorem rawHalfCosineEven_surjective : Function.Surjective rawHalfCosineEven := by
  intro f
  obtain ⟨v, hv⟩ := evenDilation_surjective ((2 : ℂ) • f)
  refine ⟨evenFourier.symm v, ?_⟩
  apply Subtype.ext
  change (1 / 2 : ℂ) • dilation
    (evenFourier (evenFourier.symm v) : ComplexL2) = (f : ComplexL2)
  rw [evenFourier.apply_symm_apply]
  have hv' : dilation (v : ComplexL2) = (2 : ℂ) • (f : ComplexL2) :=
    congrArg (fun z : evenL2 => (z : ComplexL2)) hv
  rw [hv', smul_smul]
  norm_num

/-- Exact profile-to-height identification with the literal raw t variable. -/
theorem rawHalfCosine_evenKProfile (q : ℝ) (hq : 0 < q) :
    rawHalfCosine (evenKProfile q hq) = (evenKHeight q hq : ComplexL2) := by
  apply Lp.ext
  have hraw := rawHalfCosine_toLp_ae (kEvenProfile_integrable hq)
    (kEvenProfile_memLp_two hq) (kEvenProfile_neg q)
  refine (hraw.trans (Filter.Eventually.of_forall fun t => ?_)).trans
    (evenKHeight_coe_ae q hq).symm
  exact (halfCosineTransform_eq_half_fourier
    (kEvenProfile_integrable hq) (kEvenProfile_neg q) t).trans
      (imaginaryOrderK_eq_half_fourier t q hq).symm

/-- Extension to all ambient classes only to take closed linear preimages.
It first applies the already explicit even projection. -/
def rawHalfCosineAmbient : ComplexL2 →L[ℂ] ComplexL2 :=
  rawHalfCosine.comp (evenProjection.codRestrict evenL2 evenProjection_mem)

private theorem evenProjectionSubspace_self (f : evenL2) :
    evenProjectionSubspace (f : ComplexL2) = f := by
  apply Subtype.ext
  exact evenProjection_eq_self f.property

private theorem rawHalfCosineAmbient_even (f : evenL2) :
    rawHalfCosineAmbient (f : ComplexL2) = rawHalfCosine f := by
  change rawHalfCosine (evenProjectionSubspace (f : ComplexL2)) = rawHalfCosine f
  rw [evenProjectionSubspace_self]

/-- Literal K-height class at q=n+1, represented by t -> K_{2it}(n+1). -/
def integerHeight (n : ℕ) : ComplexL2 :=
  (evenKHeight ((n : ℝ) + 1) (by positivity) : ComplexL2)

theorem integerHeight_coe_ae (n : ℕ) :
    (integerHeight n : ℝ → ℂ) =ᵐ[volume]
      fun t : ℝ => (imaginaryOrderK t ((n : ℝ) + 1) : ℂ) :=
  evenKHeight_coe_ae ((n : ℝ) + 1) (by positivity)

def integerHeightSpan : Submodule ℂ ComplexL2 :=
  Submodule.span ℂ (Set.range integerHeight)

private theorem rawHalfCosineAmbient_integerProfile (n : ℕ) :
    rawHalfCosineAmbient (integerProfile n) = integerHeight n := by
  change rawHalfCosineAmbient
    (evenKProfile ((n : ℝ) + 1) (by positivity) : ComplexL2) = _
  rw [rawHalfCosineAmbient_even, rawHalfCosine_evenKProfile]
  rfl

/-- Spatial density is transported using a closed continuous linear
preimage, with every generator identified with its actual K-height class. -/
theorem rawHalfCosine_mem_integerHeightClosure (f : evenL2) :
    rawHalfCosine f ∈ integerHeightSpan.topologicalClosure := by
  let C : Submodule ℂ ComplexL2 :=
    integerHeightSpan.topologicalClosure.comap rawHalfCosineAmbient.toLinearMap
  have hC : IsClosed (C : Set ComplexL2) :=
    isClosed_closure.preimage rawHalfCosineAmbient.continuous
  have hspan : integerProfileSpan ≤ C := by
    apply Submodule.span_le.2
    rintro v ⟨n, rfl⟩
    change rawHalfCosineAmbient (integerProfile n) ∈
      integerHeightSpan.topologicalClosure
    rw [rawHalfCosineAmbient_integerProfile]
    change integerHeight n ∈ closure (integerHeightSpan : Set ComplexL2)
    exact subset_closure (Submodule.subset_span (Set.mem_range_self n))
  have hclosure : integerProfileSpan.topologicalClosure ≤ C :=
    closure_minimal
      (show (integerProfileSpan : Set ComplexL2) ⊆ (C : Set ComplexL2) from hspan) hC
  have hf := hclosure (evenL2_le_integerProfileClosure f.property)
  change rawHalfCosineAmbient (f : ComplexL2) ∈
    integerHeightSpan.topologicalClosure at hf
  rw [rawHalfCosineAmbient_even] at hf
  exact hf

/-- Dense span of actual raw K-height profiles at positive integer q.
The measure on the height axis is literal Lebesgue dt. -/
theorem integerHeightClosure_eq_evenL2 :
    integerHeightSpan.topologicalClosure = evenL2 := by
  have hspan : integerHeightSpan ≤ evenL2 := by
    apply Submodule.span_le.2
    rintro v ⟨n, rfl⟩
    exact (evenKHeight ((n : ℝ) + 1) (by positivity)).property
  apply le_antisymm
  · exact closure_minimal
      (show (integerHeightSpan : Set ComplexL2) ⊆ (evenL2 : Set ComplexL2) from hspan)
      isClosed_evenL2
  · intro f hf
    obtain ⟨g, hg⟩ := rawHalfCosineEven_surjective (⟨f, hf⟩ : evenL2)
    have hg' : rawHalfCosine g = f :=
      congrArg (fun z : evenL2 => (z : ComplexL2)) hg
    rw [← hg']
    exact rawHalfCosine_mem_integerHeightClosure g

/-- The full positive-q height family, still in ordinary raw-height L2. -/
def positiveHeightSpan : Submodule ℂ ComplexL2 :=
  Submodule.span ℂ (Set.range fun q : {q : ℝ // 0 < q} =>
    (evenKHeight q.val q.property : ComplexL2))

theorem positiveHeightClosure_eq_evenL2 :
    positiveHeightSpan.topologicalClosure = evenL2 := by
  have hspan : positiveHeightSpan ≤ evenL2 := by
    apply Submodule.span_le.2
    rintro v ⟨q, rfl⟩
    exact (evenKHeight q.val q.property).property
  have hint : integerHeightSpan ≤ positiveHeightSpan := by
    apply Submodule.span_le.2
    rintro v ⟨n, rfl⟩
    exact Submodule.subset_span ⟨⟨(n : ℝ) + 1, by positivity⟩, rfl⟩
  apply le_antisymm
  · exact closure_minimal
      (show (positiveHeightSpan : Set ComplexL2) ⊆ (evenL2 : Set ComplexL2) from hspan)
      isClosed_evenL2
  · intro f hf
    have hfi : f ∈ closure (integerHeightSpan : Set ComplexL2) := by
      rw [← integerHeightClosure_eq_evenL2] at hf
      exact hf
    exact closure_mono
      (show (integerHeightSpan : Set ComplexL2) ⊆ (positiveHeightSpan : Set ComplexL2)
        from hint) hfi

end ImbalancedChen.Part3.ActualKHeightTotalitySourceOnly
