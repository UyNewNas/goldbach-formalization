import ImbalancedChen.Part3MaassFiniteCoreResolventCoercivity
import Mathlib.MeasureTheory.Measure.OpenPos

/-!
SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED, 2026-10-25.

The actual finite-coordinate Maass operator has a well-defined graph in
canonical hyperbolic L². Both coordinates of this graph are proved L².
A.e. equality of its continuous input functions implies pointwise equality
because the actual canonical volume has full support. Existing coordinate
derivative representation independence then gives equality of the outputs.
No graph closure, dense domain, self-adjointness or spectral theorem is asserted.
-/

namespace ImbalancedChen.Part3.MaassFiniteCoreL2Graph20261025a

noncomputable section

open MeasureTheory
open ImbalancedChen.Part3.CanonicalTensorHyperbolicLaplacianForm20261024z
open ImbalancedChen.Part3.MaassWeakOperatorCore20261024zz
open ImbalancedChen.Part3.MaassFiniteCoreResolventCoercivity20261025a

/-- Canonical hyperbolic volume is positive on every nonempty open set.
The proof uses the actual positive height density and the open embedding
of the upper half-plane into ℂ. -/
theorem canonical_volume_isOpenPosMeasure :
    (volume : Measure UpperHalfPlane).IsOpenPosMeasure := by
  letI : ((volume : Measure ℂ).comap UpperHalfPlane.coe).IsOpenPosMeasure :=
    Measure.IsOpenPosMeasure.comap (volume : Measure ℂ) UpperHalfPlane.isOpenEmbedding_coe
  have hpos (z : UpperHalfPlane) : upperDensityNN z ≠ 0 := by
    have hheight : (NNReal.mk z.im z.im_pos.le : ℝ≥0) ≠ 0 := by
      have hp : (0 : ℝ≥0) < NNReal.mk z.im z.im_pos.le := z.im_pos
      exact hp.ne'
    exact pow_ne_zero 2 (div_ne_zero one_ne_zero hheight)
  have hac : ((volume : Measure ℂ).comap UpperHalfPlane.coe) ≪
      (volume : Measure UpperHalfPlane) := by
    change ((volume : Measure ℂ).comap UpperHalfPlane.coe) ≪
      (((volume : Measure ℂ).comap UpperHalfPlane.coe).withDensity
        (fun z => (upperDensityNN z : ℝ≥0∞)))
    apply withDensity_absolutelyContinuous'
      upperDensityNN_measurable.coe_nnreal_ennreal.aemeasurable
    exact Filter.Eventually.of_forall fun z => by exact_mod_cast hpos z
  exact hac.isOpenPosMeasure

theorem continuous_finiteCoreFunction {ι : Type*}
    (s : Finset ι) (T : ι → CompactTensor) : Continuous (finiteCoreFunction s T) := by
  change Continuous (fun z : UpperHalfPlane =>
    ∑ i ∈ s, tensorFunctionH (T i).horizontal (T i).vertical z)
  apply continuous_finsetSum s
  intro i _
  simpa only [tensorFunctionH_eq] using
    (((T i).horizontal_smooth.continuous.comp UpperHalfPlane.continuous_re).mul
      ((T i).vertical_smooth.continuous.comp UpperHalfPlane.continuous_im))

/-- Equality in the actual a.e. quotient detects equality of continuous
finite tensor functions; no faithfulness assumption is supplied. -/
theorem finiteCoreFunction_eq_of_ae_eq {ι κ : Type*}
    (s : Finset ι) (T : ι → CompactTensor)
    (t : Finset κ) (U : κ → CompactTensor)
    (h : finiteCoreFunction s T =ᵐ[(volume : Measure UpperHalfPlane)]
      finiteCoreFunction t U) :
    finiteCoreFunction s T = finiteCoreFunction t U := by
  letI := canonical_volume_isOpenPosMeasure
  exact Measure.eq_of_ae_eq h (continuous_finiteCoreFunction s T)
    (continuous_finiteCoreFunction t U)

/-- A.e. equality of actual core functions forces pointwise equality of
their coordinate Laplacians. This is the required a.e. descent lemma. -/
theorem finiteCoreLaplacian_eq_of_ae_eq {ι κ : Type*}
    (s : Finset ι) (T : ι → CompactTensor)
    (t : Finset κ) (U : κ → CompactTensor)
    (h : finiteCoreFunction s T =ᵐ[(volume : Measure UpperHalfPlane)]
      finiteCoreFunction t U) :
    finiteCoreLaplacian s T = finiteCoreLaplacian t U :=
  finiteCoreLaplacian_representation_independent s T t U
    (finiteCoreFunction_eq_of_ae_eq s T t U h)

theorem finiteCoreLaplacian_ae_zero_of_input_ae_zero {ι : Type*}
    (s : Finset ι) (T : ι → CompactTensor)
    (h : finiteCoreFunction s T =ᵐ[(volume : Measure UpperHalfPlane)] 0) :
    finiteCoreLaplacian s T =ᵐ[(volume : Measure UpperHalfPlane)] 0 := by
  have hin : finiteCoreFunction s T =ᵐ[(volume : Measure UpperHalfPlane)]
      finiteCoreFunction (∅ : Finset ι) T := by
    simpa only [finiteCoreFunction, Finset.sum_empty] using h
  have hout := finiteCoreLaplacian_eq_of_ae_eq s T (∅ : Finset ι) T hin
  have hz : finiteCoreLaplacian s T = 0 := by
    simpa only [finiteCoreLaplacian, Finset.sum_empty] using hout
  exact Filter.Eventually.of_forall fun z => congrFun hz z

private theorem star_mul_self_complex (c : ℂ) :
    star c * c = ((‖c‖ ^ 2 : ℝ) : ℂ) := by
  calc
    star c * c = (Complex.normSq c : ℂ) := by
      simpa only [Complex.star_def] using (Complex.normSq_eq_conj_mul_self (z := c)).symm
    _ = ((‖c‖ ^ 2 : ℝ) : ℂ) := by rw [Complex.normSq_eq_norm_sq]

/-- Continuous compact separated factors need no fourth derivatives to
belong to hyperbolic L². This also applies to the second derivatives in Δ. -/
theorem separated_memLp (u v : ℝ → ℂ)
    (hu : Continuous u) (hv : Continuous v)
    (huc : HasCompactSupport u) (hvc : HasCompactSupport v)
    (hvpos : tsupport v ⊆ Set.Ioi (0 : ℝ)) :
    MemLp (tensorFunctionH u v) 2 (volume : Measure UpperHalfPlane) := by
  have hx : Integrable (fun x : ℝ => star (u x) * u x) :=
    (hu.star.mul hu).integrable_of_hasCompactSupport huc.mul_left
  have hy : Integrable (fun y : ℝ =>
      star (divideHeight v y) * divideHeight v y) :=
    ((continuous_divideHeight v hv hvpos).star.mul
      (continuous_divideHeight v hv hvpos)).integrable_of_hasCompactSupport
        (hasCompactSupport_divideHeight v hvc).mul_left
  have hbase := hx.mul_prod hy
  have hchart : Integrable (fun p : ℝ × ℝ =>
      star (tensorFunction u v p) * tensorFunction u v p) chartMeasure := by
    unfold chartMeasure
    apply (integrable_withDensity_iff_integrable_smul chartWeight_measurable).2
    apply (hbase.integrableOn upperChart).congr
    apply Filter.Eventually.of_forall
    intro p
    simp only [NNReal.smul_def, Complex.real_smul]
    change (star (u p.1) * u p.1) *
        (star (((p.2⁻¹ : ℝ) : ℂ) * v p.2) *
          (((p.2⁻¹ : ℝ) : ℂ) * v p.2)) =
      (((p.2⁻¹) ^ 2 : ℝ) : ℂ) *
        (star (u p.1 * v p.2) * (u p.1 * v p.2))
    push_cast
    simp only [star_mul, Complex.star_def, map_mul, Complex.conj_ofReal]
    ring
  have hmass := canonical_integrable_of_chart_integrable _ hchart
  have hsquare : Integrable (fun z : UpperHalfPlane => ‖tensorFunctionH u v z‖ ^ 2) := by
    simpa only [tensorFunctionH, star_mul_self_complex, Complex.ofReal_re] using hmass.re
  have hcont : Continuous (tensorFunctionH u v) := by
    simpa only [tensorFunctionH_eq] using
      ((hu.comp UpperHalfPlane.continuous_re).mul (hv.comp UpperHalfPlane.continuous_im))
  exact (memLp_two_iff_integrable_sq_norm hcont.aestronglyMeasurable).2 hsquare

private theorem second_derivative_continuous (u : ℝ → ℂ) (hu : ContDiff ℝ 2 u) :
    Continuous (deriv (deriv u)) := by
  have hs : ContDiff ℝ ((1 : ℕ∞ω) + 1) u := by simpa using hu
  exact (contDiff_succ_iff_deriv.mp hs).2.2.continuous_deriv_one

/-- The actual Laplacian of each compact C² tensor belongs to canonical
L². Its two terms use continuous compact second derivatives only. -/
theorem tensorLaplacian_memLp (T : CompactTensor) :
    MemLp (tensorHyperbolicLaplacianH T.horizontal T.vertical) 2
      (volume : Measure UpperHalfPlane) := by
  have hx := separated_memLp (deriv (deriv T.horizontal))
    (fun y : ℝ => (y : ℂ) ^ 2 * T.vertical y)
    (second_derivative_continuous T.horizontal T.horizontal_smooth)
    ((Complex.continuous_ofReal.pow 2).mul T.vertical_smooth.continuous)
    T.horizontal_compact.deriv.deriv T.vertical_compact.mul_left
    (tsupport_mul_subset_right.trans T.vertical_positive)
  have hy := separated_memLp T.horizontal
    (fun y : ℝ => (y : ℂ) ^ 2 * deriv (deriv T.vertical) y)
    T.horizontal_smooth.continuous
    ((Complex.continuous_ofReal.pow 2).mul
      (second_derivative_continuous T.vertical T.vertical_smooth))
    T.horizontal_compact T.vertical_compact.deriv.deriv.mul_left
    (tsupport_mul_subset_right.trans
      (tsupport_deriv_subset.trans (tsupport_deriv_subset.trans T.vertical_positive)))
  have heq : tensorHyperbolicLaplacianH T.horizontal T.vertical =
      -(tensorFunctionH (deriv (deriv T.horizontal))
          (fun y : ℝ => (y : ℂ) ^ 2 * T.vertical y) +
        tensorFunctionH T.horizontal
          (fun y : ℝ => (y : ℂ) ^ 2 * deriv (deriv T.vertical) y)) := by
    funext z
    simp only [tensorHyperbolicLaplacianH, tensorHyperbolicLaplacian,
      tensorFunctionH, tensorFunction, Pi.neg_apply, Pi.add_apply]
    ring
  rw [heq]
  exact (hx.add hy).neg

theorem finiteCoreLaplacian_memLp {ι : Type*}
    (s : Finset ι) (T : ι → CompactTensor) :
    MemLp (finiteCoreLaplacian s T) 2 (volume : Measure UpperHalfPlane) :=
  memLp_finsetSum s (fun i _ => tensorLaplacian_memLp (T i))

abbrev HyperbolicL2 := Lp ℂ 2 (volume : Measure UpperHalfPlane)

def finiteCoreL2 {ι : Type*} (s : Finset ι) (T : ι → CompactTensor) : HyperbolicL2 :=
  (finiteCoreFunction_memLp s T).toLp (finiteCoreFunction s T)

def finiteCoreLaplacianL2 {ι : Type*} (s : Finset ι)
    (T : ι → CompactTensor) : HyperbolicL2 :=
  (finiteCoreLaplacian_memLp s T).toLp (finiteCoreLaplacian s T)

/-- The graph descends to the actual L² quotient, with no chosen
representative or same-target well-definedness premise. -/
theorem finiteCoreLaplacianL2_eq_of_input_eq {ι κ : Type*}
    (s : Finset ι) (T : ι → CompactTensor)
    (t : Finset κ) (U : κ → CompactTensor)
    (h : finiteCoreL2 s T = finiteCoreL2 t U) :
    finiteCoreLaplacianL2 s T = finiteCoreLaplacianL2 t U := by
  have hin := (MemLp.toLp_eq_toLp_iff (finiteCoreFunction_memLp s T)
    (finiteCoreFunction_memLp t U)).mp h
  have hout := finiteCoreLaplacian_eq_of_ae_eq s T t U hin
  unfold finiteCoreLaplacianL2
  exact MemLp.toLp_congr _ _ (Filter.Eventually.of_forall fun z => congrFun hout z)

/-- An actual graph in the product of canonical hyperbolic L² spaces. -/
def finiteTensorL2Graph : Set (HyperbolicL2 × HyperbolicL2) :=
  {p | ∃ (n : ℕ) (T : Fin n → CompactTensor),
    p.1 = finiteCoreL2 Finset.univ T ∧
      p.2 = finiteCoreLaplacianL2 Finset.univ T}

theorem finiteTensorL2Graph_right_unique {f g h : HyperbolicL2}
    (hfg : (f, g) ∈ finiteTensorL2Graph) (hfh : (f, h) ∈ finiteTensorL2Graph) : g = h := by
  rcases hfg with ⟨n, T, hf, hg⟩
  rcases hfh with ⟨m, U, hf', hh⟩
  rw [hg, hh]
  exact finiteCoreLaplacianL2_eq_of_input_eq Finset.univ T Finset.univ U (hf.symm.trans hf')

end

end ImbalancedChen.Part3.MaassFiniteCoreL2Graph20261025a
