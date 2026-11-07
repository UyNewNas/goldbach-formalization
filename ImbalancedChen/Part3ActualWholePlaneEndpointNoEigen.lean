import ImbalancedChen.Part3ActualPlanarTensorL2Norm
import ImbalancedChen.Part3RealLineZeroMeanDerivativeDensity
import ImbalancedChen.Part3ActualResolventCyclicIntertwining
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-!
CODE_ONLY / SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED, 2026-10-25.
True whole-line horizontal L2 uniqueness from actual compact derivative
density and actual supported-plane tensor density. It closes the actual
whole-upper-half-plane resolvent endpoint eigenspace and actual scalar
endpoint atom, including the genuine lambda=1/t-1 pushforward atom.
-/

noncomputable section

namespace ImbalancedChen.Part3.ActualWholePlaneEndpointNoEigenSourceOnly

open MeasureTheory Set Filter
open MaassWeakOperatorCore20261024zz MaassFiniteCoreL2Graph20261025a
open MaassFirstGradientWeakLimit20261025a MaassFirstGradientClosability20261025a
open ActualCompletedTensorEnergyForm20261025a ActualCompletedEnergyResolvent20261025a
open CanonicalPlanarL2UnitarySourceOnly ActualWholePlaneSpectralFloorSourceOnly
open ActualHorizontalGreenTensorTestsSourceOnly ActualPlanarTensorL2NormSourceOnly
open RealLineZeroMeanDerivativeDensity20261025a
open ActualResolventScalarMeasure20261025a ActualResolventZeroAtomPushforward20261025a
open ActualResolventContinuousCyclic20261025a ActualResolventCyclicL2Representation20261025a
open ActualResolventCyclicIntertwining20261025a

/-- One-dimensional genuine compact derivative approximation is transported
with the exact planar tensor norm. This annihilates every compact horizontal
factor, not only those which happen to be derivatives. -/
theorem horizontal_zero_planeTensor_pairing (u : completedEnergy)
    (hx : completedGradient false u = 0) (g v : ℝ → ℂ)
    (hg : Continuous g) (hgc : HasCompactSupport g) (hv : ContDiff ℝ 2 v)
    (hvc : HasCompactSupport v) (hpos : tsupport v ⊆ Ioi (0 : ℝ)) :
    inner ℂ (forwardL2 (physicalProjection u))
      (planeTensorL2 g v hg hgc hv.continuous hvc) = 0 := by
  let W : PlaneL2 := forwardL2 (physicalProjection u)
  let A : PlaneL2 := planeTensorL2 g v hg hgc hv.continuous hvc
  change inner ℂ W A = 0
  by_contra hnot
  have hA : 0 < ‖inner ℂ W A‖ := norm_pos_iff.mpr hnot
  let C : ℝ := ‖W‖ * ‖lineL2 v hv.continuous hvc‖
  have hC : 0 ≤ C := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  let δ : ℝ := ‖inner ℂ W A‖ / (C + 1)
  have hden : 0 < C + 1 := by positivity
  have hδ : 0 < δ := div_pos hA hden
  obtain ⟨h, hder, hh, hhc, hnear⟩ := exists_compact_smooth_derivative_approximation g
    (hg.memLp_of_hasCompactSupport hgc) δ hδ
  have hh2 : ContDiff ℝ 2 h := hh.of_le (by simp)
  have hh1 : ContDiff ℝ 1 h := hh2.of_le (by norm_num)
  have hdc : Continuous (deriv h) := hh1.continuous_deriv_one
  let B : PlaneL2 := planeTensorL2 (deriv h) v hdc hhc.deriv hv.continuous hvc
  have hB : inner ℂ W B = 0 :=
    horizontal_zero_derivative_tensor_pairing u hx h v hh2 hhc hv hvc hpos
  have hn : ‖lineL2 g hg hgc - lineL2 (deriv h) hdc hhc.deriv‖ < δ := hnear
  have hdist : ‖A - B‖ =
      ‖lineL2 g hg hgc - lineL2 (deriv h) hdc hhc.deriv‖ * ‖lineL2 v hv.continuous hvc‖ :=
    planeTensorL2_distance g (deriv h) v hg hgc hdc hhc.deriv hv.continuous hvc
  have hbound : ‖inner ℂ W A‖ ≤ C * δ := by
    calc
      _ = ‖inner ℂ W (A - B)‖ := by rw [inner_sub_right, hB, sub_zero]
      _ ≤ ‖W‖ * ‖A - B‖ := norm_inner_le_norm _ _
      _ = C * ‖lineL2 g hg hgc - lineL2 (deriv h) hdc hhc.deriv‖ := by
        rw [hdist]
        dsimp [C]
        ring
      _ ≤ C * δ := mul_le_mul_of_nonneg_left hn.le hC
  have hδeq : δ * (C + 1) = ‖inner ℂ W A‖ :=
    div_mul_cancel₀ _ (ne_of_gt hden)
  have hstrict : C * δ < ‖inner ℂ W A‖ := by nlinarith
  exact (not_lt_of_ge hbound) hstrict

/-- Pairings vanish against the actual CompactTensor tests used in the
already proved upper-supported planar tensor-density theorem. -/
theorem horizontal_zero_actual_plane_tests (u : completedEnergy)
    (hx : completedGradient false u = 0) (T : CompactTensor) :
    inner ℂ (forwardL2 (physicalProjection u)) (testL2 T) = 0 :=
  horizontal_zero_planeTensor_pairing u hx T.horizontal T.vertical
    T.horizontal_smooth.continuous T.horizontal_compact T.vertical_smooth
    T.vertical_compact T.vertical_positive

/-- Genuine whole-line horizontal weak derivative zero implies the actual
physical canonical L2 input is zero. Infinite horizontal extent enters
through the proved compact-derivative L2 density, not a constant-function
exclusion assumption. -/
theorem horizontal_zero_physical_zero (u : completedEnergy)
    (hx : completedGradient false u = 0) : physicalProjection u = 0 := by
  have hW : forwardL2 (physicalProjection u) = 0 :=
    upperSupported_eq_zero_of_test_pairings _
      (forwardL2_mem_upperSupported (physicalProjection u))
      (horizontal_zero_actual_plane_tests u hx)
  have hunit : canonicalPlanarUnitary (physicalProjection u) = 0 := Subtype.ext hW
  exact canonicalPlanarUnitary.injective (hunit.trans (map_zero canonicalPlanarUnitary).symm)

theorem horizontal_zero_completed_zero (u : completedEnergy)
    (hx : completedGradient false u = 0) : u = 0 := by
  apply physicalProjection_injective
  rw [horizontal_zero_physical_zero u hx, map_zero]

/-- The actual whole-upper-half-plane resolvent has no nonzero endpoint
4/5 eigenvector. Strict core Hardy is not used. -/
theorem endpoint_eigen_eq_zero {f : HyperbolicL2}
    (heigen : actualWeakResolvent f = (4 / 5 : ℂ) • f) : f = 0 := by
  have hx := endpoint_eigen_horizontal_gradient_zero heigen
  have hp := horizontal_zero_physical_zero (energyRieszSolution f) hx
  have hR : actualWeakResolvent f = 0 := (actualWeakResolvent_apply f).trans hp
  have hscalar : (4 / 5 : ℂ) • f = 0 := heigen.symm.trans hR
  exact (smul_eq_zero.mp hscalar).resolve_left (by norm_num)

/-- The actual scalar endpoint fiber, allowing an empty spectral fiber. -/
def endpointFiber : Set ResolventSpectrum := {t | (t : ℝ) = (4 / 5 : ℝ)}

theorem measurableSet_endpointFiber : MeasurableSet endpointFiber :=
  (isClosed_eq continuous_subtype_val continuous_const).measurableSet

def endpointAtomVector (f : HyperbolicL2) : ScalarL2 f :=
  indicatorConstLp 2 measurableSet_endpointFiber (measure_ne_top (scalarMeasure f) endpointFiber)
    (1 : ℂ)

theorem endpointAtomVector_coe_ae (f : HyperbolicL2) :
    (endpointAtomVector f : ResolventSpectrum → ℂ) =ᵐ[scalarMeasure f]
      endpointFiber.indicator (fun _ => (1 : ℂ)) := indicatorConstLp_coeFn

theorem endpointAtomVector_multiplier (f : HyperbolicL2) :
    coordinateMultiplier f (endpointAtomVector f) = (4 / 5 : ℂ) • endpointAtomVector f := by
  apply Lp.ext
  filter_upwards [coordinateMultiplier_coe_ae f (endpointAtomVector f),
    Lp.coeFn_smul (4 / 5 : ℂ) (endpointAtomVector f), endpointAtomVector_coe_ae f]
    with t hm hs ha
  rw [hm, hs, ha]
  by_cases ht : t ∈ endpointFiber
  · have hval : (t : ℝ) = (4 / 5 : ℝ) := ht
    have hc : ((t : ℝ) : ℂ) = (4 / 5 : ℂ) := by exact_mod_cast hval
    simp only [indicator_of_mem ht, hc, smul_eq_mul]
  · simp only [indicator_of_notMem ht, mul_zero, smul_zero]

/-- The actual cyclic L2 isometry turns a nonzero scalar endpoint atom
into a genuine operator endpoint eigenvector. The preceding real uniqueness
proof forces its actual indicator vector to vanish. -/
theorem endpointAtomVector_eq_zero (f : HyperbolicL2) : endpointAtomVector f = 0 := by
  have heigen : actualWeakResolvent (cyclicExtension f (endpointAtomVector f)) =
      (4 / 5 : ℂ) • cyclicExtension f (endpointAtomVector f) := by
    rw [← cyclicExtension_intertwine, endpointAtomVector_multiplier, map_smul]
  have hz := endpoint_eigen_eq_zero heigen
  apply norm_eq_zero.mp
  rw [← cyclicExtension_norm f (endpointAtomVector f), hz, norm_zero]

/-- No atom for the genuine RMK scalar measure at the actual endpoint. -/
theorem scalarMeasure_endpointFiber (f : HyperbolicL2) : scalarMeasure f endpointFiber = 0 := by
  have hc := endpointAtomVector_coe_ae f
  rw [endpointAtomVector_eq_zero f] at hc
  have ha : endpointFiber.indicator (fun _ => (1 : ℂ)) =ᵐ[scalarMeasure f]
      (0 : ResolventSpectrum → ℂ) :=
    hc.symm.trans (Lp.coeFn_zero ℂ 2 (scalarMeasure f))
  have hnot : ∀ᵐ t : ResolventSpectrum ∂scalarMeasure f, t ∉ endpointFiber := by
    filter_upwards [ha] with t ht
    intro hm
    have hbad : (1 : ℂ) = 0 := by simpa only [indicator_of_mem hm] using ht
    exact one_ne_zero hbad
  rw [ae_iff] at hnot
  simpa only [not_not] using hnot

theorem spectralLambda_eq_quarter_iff (t : ResolventSpectrum) :
    spectralLambda t = (1 / 4 : ℝ) ↔ (t : ℝ) = (4 / 5 : ℝ) := by
  constructor
  · intro h
    have ht : (t : ℝ) ≠ 0 := by
      intro ht
      norm_num [spectralLambda, ht] at h
    have hi : (t : ℝ)⁻¹ = (5 / 4 : ℝ) := by
      unfold spectralLambda at h
      linarith
    have hp := inv_mul_cancel₀ ht
    rw [hi] at hp
    nlinarith
  · intro h
    norm_num [spectralLambda, h]

/-- No threshold atom for the already constructed actual lambda scalar
pushforward. This is only the whole-upper-half-plane Friedrichs measure. -/
theorem unboundedScalarMeasure_quarter_atom (f : HyperbolicL2) :
    unboundedScalarMeasure f {(1 / 4 : ℝ)} = 0 := by
  have hpre : spectralLambda ⁻¹' {(1 / 4 : ℝ)} = endpointFiber := by
    ext t
    exact spectralLambda_eq_quarter_iff t
  rw [unboundedScalarMeasure, Measure.map_apply measurable_spectralLambda measurableSet_singleton,
    hpre, scalarMeasure_endpointFiber]

end ImbalancedChen.Part3.ActualWholePlaneEndpointNoEigenSourceOnly
