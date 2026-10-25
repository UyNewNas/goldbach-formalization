import ImbalancedChen.Part3CountableSigmaMeasureBundle
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

The countable disjoint-measure bundle has a genuine ONTO L2 isometry
with the Hilbert lp sum of its fiber L2 spaces. The proof constructs
both maps from representatives and proves all identities almost
everywhere. Integrability and the norm identity follow from the literal
sum of the pushforward measures, not from a supplied norm/unitary axiom.
-/

namespace ImbalancedChen.Part3.CountableSigmaL2Equivalence20261025a

noncomputable section
open Set MeasureTheory Filter
open CountableSigmaMeasureBundle20261025a
open scoped ENNReal

variable {I : Type*} [Countable I] {X : I→Type*}
  [∀ i,MeasurableSpace (X i)]

def BundleL2 (mu : ∀ i,Measure (X i)) := Lp ℂ 2 (bundleMeasure mu)
def FiberL2 (mu : ∀ i,Measure (X i)) (i : I) := Lp ℂ 2 (mu i)
def FiberSum (mu : ∀ i,Measure (X i)) := lp (FiberL2 mu) 2

theorem l2_norm_sq_integral {Y : Type*} [MeasurableSpace Y] (nu : Measure Y)
    (g : Lp ℂ 2 nu) : ‖g‖^2=∫ x,‖g x‖^2∂nu := by
  symm
  calc
    (∫ x,‖g x‖^2∂nu) = ∫ x,RCLike.re (inner ℂ (g x) (g x))∂nu := by simp
    _ = RCLike.re (inner ℂ g g) := integral_re (L2.integrable_inner g g)
    _ = ‖g‖^2 := by simp

theorem toLp_norm_sq_integral {Y : Type*} [MeasurableSpace Y]
    (nu : Measure Y) (f : Y→ℂ) (hf : MemLp f 2 nu) :
    ‖hf.toLp f‖^2=∫ x,‖f x‖^2∂nu := by
  rw [l2_norm_sq_integral]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with x hx
  rw [hx]

/-- Bochner integrability on the literal Sigma measure is precisely
fiberwise integrability plus the summable norms of the fiber integrals. -/
theorem bundle_integrable_iff {E : Type*} [NormedAddCommGroup E]
    (mu : ∀ i,Measure (X i)) (f : Sigma X→E) :
    Integrable f (bundleMeasure mu) ↔
      (∀ i,Integrable (fun x => f ⟨i,x⟩) (mu i)) ∧
      Summable (fun i => ∫ x,‖f ⟨i,x⟩‖∂mu i) := by
  rw [bundleMeasure,integrable_sum_measure_iff]
  constructor
  · rintro ⟨hf,hs⟩
    refine ⟨fun i => (sigmaMk_measurableEmbedding i).integrable_map_iff.mp (hf i), ?_⟩
    convert hs using 1
    funext i
    exact ((sigmaMk_measurableEmbedding i).integral_map (fun s => ‖f s‖)).symm
  · rintro ⟨hf,hs⟩
    refine ⟨fun i => (sigmaMk_measurableEmbedding i).integrable_map_iff.mpr (hf i), ?_⟩
    convert hs using 1
    funext i
    exact (sigmaMk_measurableEmbedding i).integral_map (fun s => ‖f s‖)

theorem bundle_integral (mu : ∀ i,Measure (X i)) (f : Sigma X→ℝ)
    (hf : Integrable f (bundleMeasure mu)) :
    (∫ s,f s∂bundleMeasure mu)=∑' i,∫ x,f ⟨i,x⟩∂mu i := by
  rw [bundleMeasure] at hf ⊢
  rw [integral_sum_measure hf]
  apply tsum_congr
  intro i
  exact (sigmaMk_measurableEmbedding i).integral_map f

/-- A useful norm-free integrability criterion, including the global
summability condition rather than just separate fiber membership. -/
theorem bundle_memLp_two_iff (mu : ∀ i,Measure (X i)) (f : Sigma X→ℂ) :
    MemLp f 2 (bundleMeasure mu) ↔
      (∀ i,MemLp (fun x => f ⟨i,x⟩) 2 (mu i)) ∧
      Summable (fun i => ∫ x,‖f ⟨i,x⟩‖^2∂mu i) := by
  constructor
  · intro hf
    have hsq := (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp hf
    obtain ⟨hi,hs⟩ := (bundle_integrable_iff mu (fun s => ‖f s‖^2)).mp hsq
    refine ⟨?_,?_⟩
    · intro i
      exact (memLp_two_iff_integrable_sq_norm
        ((bundle_aestronglyMeasurable_iff mu f).mp hf.aestronglyMeasurable i)).mpr (hi i)
    · simpa only [Real.norm_of_nonneg (sq_nonneg _)] using hs
  · rintro ⟨hi,hs⟩
    have hmeas : AEStronglyMeasurable f (bundleMeasure mu) :=
      (bundle_aestronglyMeasurable_iff mu f).mpr fun i => (hi i).aestronglyMeasurable
    apply (memLp_two_iff_integrable_sq_norm hmeas).mpr
    apply (bundle_integrable_iff mu (fun s => ‖f s‖^2)).mpr
    refine ⟨fun i => (memLp_two_iff_integrable_sq_norm (hi i).aestronglyMeasurable).mp (hi i),?_⟩
    simpa only [Real.norm_of_nonneg (sq_nonneg _)] using hs

def fiberMemLp (mu : ∀ i,Measure (X i)) (g : BundleL2 mu) (i : I) :
    MemLp (fun x => g ⟨i,x⟩) 2 (mu i) :=
  ((bundle_memLp_two_iff mu g).mp (Lp.memLp g)).1 i

def restrictFiber (mu : ∀ i,Measure (X i)) (g : BundleL2 mu) (i : I) : FiberL2 mu i :=
  (fiberMemLp mu g i).toLp (fun x => g ⟨i,x⟩)

theorem restrictFiber_coe (mu : ∀ i,Measure (X i)) (g : BundleL2 mu) (i : I) :
    restrictFiber mu g i =ᵐ[mu i] fun x => g ⟨i,x⟩ :=
  (fiberMemLp mu g i).coeFn_toLp

theorem restrictFiber_memℓp (mu : ∀ i,Measure (X i)) (g : BundleL2 mu) :
    Memℓp (restrictFiber mu g) 2 := by
  apply (memℓp_gen_iff (by norm_num : 0<(2:ℝ≥0∞).toReal)).mpr
  have hs := ((bundle_memLp_two_iff mu g).mp (Lp.memLp g)).2
  simpa only [ENNReal.toReal_ofNat,Real.rpow_two,
    restrictFiber,toLp_norm_sq_integral] using hs

def restrict (mu : ∀ i,Measure (X i)) (g : BundleL2 mu) : FiberSum mu :=
  ⟨restrictFiber mu g,restrictFiber_memℓp mu g⟩

theorem restrict_coe (mu : ∀ i,Measure (X i)) (g : BundleL2 mu) (i : I) :
    restrict mu g i =ᵐ[mu i] fun x => g ⟨i,x⟩ := restrictFiber_coe mu g i

def assembleFunction (mu : ∀ i,Measure (X i)) (g : FiberSum mu) : Sigma X→ℂ :=
  fun s => g s.1 s.2

theorem assembleFunction_memLp (mu : ∀ i,Measure (X i)) (g : FiberSum mu) :
    MemLp (assembleFunction mu g) 2 (bundleMeasure mu) := by
  apply (bundle_memLp_two_iff mu _).mpr
  refine ⟨fun i => Lp.memLp (g i),?_⟩
  have hs := (memℓp_gen_iff (by norm_num : 0<(2:ℝ≥0∞).toReal)).mp g.property
  simpa only [ENNReal.toReal_ofNat,Real.rpow_two,l2_norm_sq_integral] using hs

def assemble (mu : ∀ i,Measure (X i)) (g : FiberSum mu) : BundleL2 mu :=
  (assembleFunction_memLp mu g).toLp (assembleFunction mu g)

theorem assemble_coe (mu : ∀ i,Measure (X i)) (g : FiberSum mu) :
    assemble mu g =ᵐ[bundleMeasure mu] assembleFunction mu g :=
  (assembleFunction_memLp mu g).coeFn_toLp

theorem assemble_coe_fiber (mu : ∀ i,Measure (X i)) (g : FiberSum mu) (i : I) :
    (fun x => assemble mu g ⟨i,x⟩) =ᵐ[mu i] (g i) :=
  (bundle_ae_iff mu _).mp (assemble_coe mu g) i

theorem restrict_assemble (mu : ∀ i,Measure (X i)) (g : FiberSum mu) :
    restrict mu (assemble mu g)=g := by
  apply Subtype.ext
  funext i
  apply Lp.ext
  exact (restrict_coe mu (assemble mu g) i).trans (assemble_coe_fiber mu g i)

theorem assemble_restrict (mu : ∀ i,Measure (X i)) (g : BundleL2 mu) :
    assemble mu (restrict mu g)=g := by
  apply Lp.ext
  apply (bundle_ae_iff mu _).mpr
  intro i
  exact (assemble_coe_fiber mu (restrict mu g) i).trans (restrict_coe mu g i)

theorem assemble_norm_sq (mu : ∀ i,Measure (X i)) (g : FiberSum mu) :
    ‖assemble mu g‖^2=∑' i,‖g i‖^2 := by
  rw [assemble,toLp_norm_sq_integral]
  rw [bundle_integral mu _ ((memLp_two_iff_integrable_sq_norm
    (assembleFunction_memLp mu g).aestronglyMeasurable).mp (assembleFunction_memLp mu g))]
  apply tsum_congr
  intro i
  exact (l2_norm_sq_integral (mu i) (g i)).symm

theorem assemble_norm (mu : ∀ i,Measure (X i)) (g : FiberSum mu) :
    ‖assemble mu g‖=‖g‖ := by
  have hs : ‖assemble mu g‖^2=‖g‖^2 := by
    rw [assemble_norm_sq]
    simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using
      (lp.norm_rpow_eq_tsum (by norm_num : 0<(2:ℝ≥0∞).toReal) g).symm
  nlinarith [norm_nonneg (assemble mu g),norm_nonneg g]

def assembleLinear (mu : ∀ i,Measure (X i)) : FiberSum mu→ₗ[ℂ]BundleL2 mu where
  toFun := assemble mu
  map_add' := by
    intro g h
    apply Lp.ext
    apply (bundle_ae_iff mu _).mpr
    intro i
    have hout := (bundle_ae_iff mu _).mp
      (Lp.coeFn_add (assemble mu g) (assemble mu h)) i
    filter_upwards [assemble_coe_fiber mu (g+h) i,assemble_coe_fiber mu g i,
      assemble_coe_fiber mu h i,hout,
      Lp.coeFn_add (g i) (h i)] with x hx hg hh ha hi
    calc
      assemble mu (g+h) ⟨i,x⟩ = (g+h) i x := hx
      _ = g i x+h i x := hi
      _ = assemble mu g ⟨i,x⟩+assemble mu h ⟨i,x⟩ := by rw [hg,hh]
      _ = (assemble mu g+assemble mu h) ⟨i,x⟩ := ha.symm
  map_smul' := by
    intro c g
    apply Lp.ext
    apply (bundle_ae_iff mu _).mpr
    intro i
    have hout := (bundle_ae_iff mu _).mp (Lp.coeFn_smul c (assemble mu g)) i
    filter_upwards [assemble_coe_fiber mu (c•g) i,assemble_coe_fiber mu g i,
      hout,Lp.coeFn_smul c (g i)] with x hx hg ho hi
    calc
      assemble mu (c•g) ⟨i,x⟩ = (c•g) i x := hx
      _ = c•g i x := hi
      _ = c•assemble mu g ⟨i,x⟩ := by rw [hg]
      _ = (c•assemble mu g) ⟨i,x⟩ := ho.symm

def assembleIsometry (mu : ∀ i,Measure (X i)) : FiberSum mu→ₗᵢ[ℂ]BundleL2 mu :=
  { assembleLinear mu with norm_map' := assemble_norm mu }

/-- ONTO, with the explicitly constructed inverse given by restriction
to the original fiber measures. No density or Plancherel premise. -/
def sigmaL2Equivalence (mu : ∀ i,Measure (X i)) :
    FiberSum mu≃ₗᵢ[ℂ]BundleL2 mu :=
  LinearIsometryEquiv.ofSurjective (assembleIsometry mu)
    (fun g => ⟨restrict mu g,assemble_restrict mu g⟩)

theorem sigmaL2Equivalence_apply (mu : ∀ i,Measure (X i)) (g : FiberSum mu) :
    sigmaL2Equivalence mu g=assemble mu g := rfl

theorem sigmaL2Equivalence_symm_apply (mu : ∀ i,Measure (X i)) (g : BundleL2 mu) :
    (sigmaL2Equivalence mu).symm g=restrict mu g := by
  apply (sigmaL2Equivalence mu).injective
  rw [LinearIsometryEquiv.apply_symm_apply,sigmaL2Equivalence_apply,assemble_restrict]

theorem sigmaL2Equivalence_fiber (mu : ∀ i,Measure (X i)) (g : FiberSum mu) (i : I) :
    (fun x => sigmaL2Equivalence mu g ⟨i,x⟩)=ᵐ[mu i] (g i) :=
  assemble_coe_fiber mu g i

theorem sigmaL2Equivalence_symm_fiber (mu : ∀ i,Measure (X i)) (g : BundleL2 mu) (i : I) :
    (sigmaL2Equivalence mu).symm g i=ᵐ[mu i] (fun x => g ⟨i,x⟩) := by
  rw [sigmaL2Equivalence_symm_apply]
  exact restrict_coe mu g i

end
end ImbalancedChen.Part3.CountableSigmaL2Equivalence20261025a
