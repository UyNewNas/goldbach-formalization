import ImbalancedChen.Part3MaassWeakOperatorCore
import Mathlib.MeasureTheory.Function.L2Space

/-!
SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED, 2026-10-25.

Coercivity for the actual shifted coordinate Maass operator on the finite
compact tensor core. Mass integrability is proved under canonical hyperbolic
volume, including the potentially singular factor y^{-1}; it is not assumed.
The conclusion includes triviality of the shifted kernel in the a.e. quotient.
This does not construct a closed operator or assert a spectral theorem.
-/

namespace ImbalancedChen.Part3.MaassFiniteCoreResolventCoercivity20261025a

noncomputable section

open MeasureTheory
open ImbalancedChen.Part3.CanonicalTensorHyperbolicLaplacianForm20261024z
open ImbalancedChen.Part3.MaassWeakOperatorCore20261024zz

/-- The height factor which removes hyperbolic volume from a tensor. -/
def divideHeight (v : ℝ → ℂ) (y : ℝ) : ℂ :=
  ((y⁻¹ : ℝ) : ℂ) * v y

/-- Positive-height support removes the apparent singularity at zero. -/
theorem continuous_divideHeight (v : ℝ → ℂ) (hv : Continuous v)
    (hvpos : tsupport v ⊆ Set.Ioi (0 : ℝ)) :
    Continuous (divideHeight v) := by
  apply continuous_iff_continuousAt.2
  intro y
  by_cases hy : y = 0
  · subst y
    have hzero : (0 : ℝ) ∉ tsupport v := by
      intro h
      exact (lt_irrefl (0 : ℝ)) (hvpos h)
    have hev : v =ᶠ[nhds (0 : ℝ)] 0 := by
      rwa [← notMem_tsupport_iff_eventuallyEq]
    apply (continuousAt_const : ContinuousAt (fun _ : ℝ => (0 : ℂ)) 0).congr_of_eventuallyEq
    filter_upwards [hev] with y hy
    simp [divideHeight, hy]
  · exact (Complex.continuous_ofReal.continuousAt.comp
      (continuousAt_id.inv₀ hy)).mul hv.continuousAt

theorem hasCompactSupport_divideHeight (v : ℝ → ℂ)
    (hvc : HasCompactSupport v) : HasCompactSupport (divideHeight v) := by
  exact hvc.mul_left

private theorem weight_mass_identity (u v a b : ℝ → ℂ) (p : ℝ × ℝ) :
    chartWeight p • (star (tensorFunction u v p) * tensorFunction a b p) =
      (star (u p.1) * a p.1) *
        (star (divideHeight v p.2) * divideHeight b p.2) := by
  simp only [NNReal.smul_def, Complex.real_smul]
  change (((p.2⁻¹) ^ 2 : ℝ) : ℂ) *
      (star (u p.1 * v p.2) * (a p.1 * b p.2)) =
    (star (u p.1) * a p.1) *
      (star (((p.2⁻¹ : ℝ) : ℂ) * v p.2) *
        (((p.2⁻¹ : ℝ) : ℂ) * b p.2))
  push_cast
  simp only [star_mul, Complex.star_def, map_mul, Complex.conj_ofReal]
  ring

/-- Cross mass integrability for actual compact tensor functions. The proof
uses product integration after removing the hyperbolic height density. -/
theorem canonical_tensor_mass_integrable (T U : CompactTensor) :
    Integrable (fun z : UpperHalfPlane =>
      star (tensorFunctionH T.horizontal T.vertical z) *
        tensorFunctionH U.horizontal U.vertical z) := by
  have hx : Integrable (fun x : ℝ =>
      star (T.horizontal x) * U.horizontal x) :=
    (T.horizontal_smooth.continuous.star.mul
      U.horizontal_smooth.continuous).integrable_of_hasCompactSupport
        U.horizontal_compact.mul_left
  have hy : Integrable (fun y : ℝ =>
      star (divideHeight T.vertical y) * divideHeight U.vertical y) :=
    ((continuous_divideHeight T.vertical T.vertical_smooth.continuous
      T.vertical_positive).star.mul
      (continuous_divideHeight U.vertical U.vertical_smooth.continuous
        U.vertical_positive)).integrable_of_hasCompactSupport
          (hasCompactSupport_divideHeight U.vertical U.vertical_compact).mul_left
  have hbase : Integrable (fun p : ℝ × ℝ =>
      (star (T.horizontal p.1) * U.horizontal p.1) *
        (star (divideHeight T.vertical p.2) * divideHeight U.vertical p.2)) :=
    hx.mul_prod hy
  have hchart : Integrable (fun p : ℝ × ℝ =>
      star (tensorFunction T.horizontal T.vertical p) *
        tensorFunction U.horizontal U.vertical p) chartMeasure := by
    unfold chartMeasure
    apply (integrable_withDensity_iff_integrable_smul chartWeight_measurable).2
    apply (hbase.integrableOn upperChart).congr
    exact Filter.Eventually.of_forall fun p =>
      (weight_mass_identity T.horizontal T.vertical U.horizontal U.vertical p).symm
  exact canonical_integrable_of_chart_integrable _ hchart

/-- Every finite tensor cross mass pairing is integrable; no L² premise is
required from the caller. -/
theorem finiteCore_mass_integrable {ι κ : Type*}
    (s : Finset ι) (T : ι → CompactTensor)
    (t : Finset κ) (U : κ → CompactTensor) :
    Integrable (fun z : UpperHalfPlane =>
      star (finiteCoreFunction s T z) * finiteCoreFunction t U z) := by
  have hsum : Integrable (fun z : UpperHalfPlane =>
      ∑ i ∈ s, ∑ j ∈ t,
        star (tensorFunctionH (T i).horizontal (T i).vertical z) *
          tensorFunctionH (U j).horizontal (U j).vertical z) :=
    integrable_finsetSum s (fun i _ =>
      integrable_finsetSum t (fun j _ => canonical_tensor_mass_integrable (T i) (U j)))
  simpa only [finiteCoreFunction, star_sum, Finset.sum_mul, Finset.mul_sum] using hsum

private theorem star_mul_self_complex (c : ℂ) :
    star c * c = ((‖c‖ ^ 2 : ℝ) : ℂ) := by
  calc
    star c * c = (Complex.normSq c : ℂ) := by
      simpa only [Complex.star_def] using (Complex.normSq_eq_conj_mul_self (z := c)).symm
    _ = ((‖c‖ ^ 2 : ℝ) : ℂ) := by rw [Complex.normSq_eq_norm_sq]

theorem finiteCore_square_norm_integrable {ι : Type*}
    (s : Finset ι) (T : ι → CompactTensor) :
    Integrable (fun z : UpperHalfPlane => ‖finiteCoreFunction s T z‖ ^ 2) := by
  simpa only [star_mul_self_complex, Complex.ofReal_re] using
    (finiteCore_mass_integrable s T s T).re

theorem finiteCoreFunction_memLp {ι : Type*}
    (s : Finset ι) (T : ι → CompactTensor) :
    MemLp (finiteCoreFunction s T) 2 (volume : Measure UpperHalfPlane) := by
  have hcont : Continuous (finiteCoreFunction s T) := by
    change Continuous (fun z : UpperHalfPlane =>
      ∑ i ∈ s, tensorFunctionH (T i).horizontal (T i).vertical z)
    apply continuous_finsetSum s
    intro i _
    simpa only [tensorFunctionH_eq] using
      (((T i).horizontal_smooth.continuous.comp UpperHalfPlane.continuous_re).mul
        ((T i).vertical_smooth.continuous.comp UpperHalfPlane.continuous_im))
  exact (memLp_two_iff_integrable_sq_norm hcont.aestronglyMeasurable).2
    (finiteCore_square_norm_integrable s T)

private theorem finiteCore_laplacian_pair_integrable {ι κ : Type*}
    (s : Finset ι) (T : ι → CompactTensor)
    (t : Finset κ) (U : κ → CompactTensor) :
    Integrable (fun z : UpperHalfPlane =>
      star (finiteCoreFunction s T z) * finiteCoreLaplacian t U z) := by
  have hsum : Integrable (fun z : UpperHalfPlane =>
      ∑ i ∈ s, ∑ j ∈ t,
        star (tensorFunctionH (T i).horizontal (T i).vertical z) *
          tensorHyperbolicLaplacianH (U j).horizontal (U j).vertical z) := by
    apply integrable_finsetSum s
    intro i _
    apply integrable_finsetSum t
    intro j _
    exact canonical_mixed_integrable _ _ _ _
      (T i).horizontal_smooth (T i).vertical_smooth
      (U j).horizontal_smooth (U j).vertical_smooth
      (U j).horizontal_compact (U j).vertical_compact
  simpa only [finiteCoreFunction, finiteCoreLaplacian,
    star_sum, Finset.sum_mul, Finset.mul_sum] using hsum

/-- `1 + Δ` on the actual finite test functions, with Δ defined by the
coordinate second derivatives in `Part3MaassWeakOperatorCore`. -/
def shiftedCoreLaplacian {ι : Type*} (s : Finset ι)
    (T : ι → CompactTensor) (z : UpperHalfPlane) : ℂ :=
  finiteCoreFunction s T z + finiteCoreLaplacian s T z

theorem shiftedCoreLaplacian_eq_upperMaass {ι : Type*}
    (s : Finset ι) (T : ι → CompactTensor) :
    shiftedCoreLaplacian s T =
      fun z => finiteCoreFunction s T z + upperMaass (finiteCoreFunction s T) z := by
  rw [upperMaass_finiteCoreFunction]
  rfl

/-- Exact shifted energy identity under canonical hyperbolic volume. -/
theorem shiftedCore_energy_identity {ι : Type*}
    (s : Finset ι) (T : ι → CompactTensor) :
    (∫ z : UpperHalfPlane,
      star (finiteCoreFunction s T z) * shiftedCoreLaplacian s T z).re =
      (∫ z : UpperHalfPlane, ‖finiteCoreFunction s T z‖ ^ 2) +
        (finiteCoreEnergy s T s T).re := by
  have hsplit : (∫ z : UpperHalfPlane,
      star (finiteCoreFunction s T z) * shiftedCoreLaplacian s T z) =
      (∫ z : UpperHalfPlane,
        star (finiteCoreFunction s T z) * finiteCoreFunction s T z) +
      (∫ z : UpperHalfPlane,
        star (finiteCoreFunction s T z) * finiteCoreLaplacian s T z) := by
    simp only [shiftedCoreLaplacian, mul_add]
    exact integral_add (finiteCore_mass_integrable s T s T)
      (finiteCore_laplacian_pair_integrable s T s T)
  rw [hsplit, Complex.add_re, canonical_weakMaass_on_finite_tensor_span]
  simp_rw [star_mul_self_complex]
  rw [integral_complex_ofReal]
  simp

/-- Concrete coercivity for the shifted actual Maass operator on the whole
finite tensor core, retaining every mixed derivative cross term. -/
theorem shiftedCore_coercive {ι : Type*}
    (s : Finset ι) (T : ι → CompactTensor) :
    (∫ z : UpperHalfPlane, ‖finiteCoreFunction s T z‖ ^ 2) ≤
      (∫ z : UpperHalfPlane,
        star (finiteCoreFunction s T z) * shiftedCoreLaplacian s T z).re := by
  rw [shiftedCore_energy_identity]
  exact le_add_of_nonneg_right (finiteCoreEnergy_nonneg s T)

/-- The shifted actual operator has trivial kernel in the Hilbert a.e.
quotient on this core. This is an injectivity fact, not surjectivity or
self-adjointness of a closure. -/
theorem shiftedCore_kernel_ae_zero {ι : Type*}
    (s : Finset ι) (T : ι → CompactTensor)
    (hzero : shiftedCoreLaplacian s T =ᵐ[(volume : Measure UpperHalfPlane)] 0) :
    finiteCoreFunction s T =ᵐ[(volume : Measure UpperHalfPlane)] 0 := by
  have hpair : (∫ z : UpperHalfPlane,
      star (finiteCoreFunction s T z) * shiftedCoreLaplacian s T z) = 0 := by
    calc
      _ = ∫ _z : UpperHalfPlane, (0 : ℂ) := by
        apply integral_congr_ae
        filter_upwards [hzero] with z hz
        simp [hz]
      _ = 0 := by simp
  have hmass : (∫ z : UpperHalfPlane, ‖finiteCoreFunction s T z‖ ^ 2) = 0 := by
    apply le_antisymm
    · simpa only [hpair, Complex.zero_re] using shiftedCore_coercive s T
    · exact integral_nonneg fun z => sq_nonneg (‖finiteCoreFunction s T z‖)
  have hsq := (integral_eq_zero_iff_of_nonneg
    (fun z : UpperHalfPlane => sq_nonneg (‖finiteCoreFunction s T z‖))
    (finiteCore_square_norm_integrable s T)).mp hmass
  filter_upwards [hsq] with z hz
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp hz)

end

end ImbalancedChen.Part3.MaassFiniteCoreResolventCoercivity20261025a
