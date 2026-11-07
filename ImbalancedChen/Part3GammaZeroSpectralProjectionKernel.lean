import ImbalancedChen.Part3GammaConstantFormClosure
import ImbalancedChen.Part3Gamma0ActualGlobalLambdaDomain
import ImbalancedChen.Part3Gamma0ActualUnboundedScalarMeasure
import ImbalancedChen.Part3GenericGlobalProjectionScalarConsistency
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

The zero spectral projection of the ACTUAL Gamma0 Friedrichs operator
is the orthogonal projection onto its ACTUAL kernel. The projection is
constructed in the true global scalar spectral model, at resolvent
coordinate r=1, exactly lambda=r^-1-1=0. No rank-one assertion or kernel
classification is assumed. The original unbounded lambda-domain graph
and the physical native graph are retained, and the scalar zero-atom
mass is exactly the squared norm of this genuine kernel projection.
-/
namespace ImbalancedChen.Part3.GammaZeroSpectralProjectionKernel20261026a

noncomputable section
open Set MeasureTheory
open Gamma0ActualSmoothQuotientCore20261025a
open Gamma0ActualWeakRieszResolvent20261025a
open Gamma0ActualFriedrichsOperator20261025a
open Gamma0ActualGlobalFriedrichsGraph20261025a
open Gamma0ActualGlobalLambdaDomain20261025a
open Gamma0ActualUnboundedScalarMeasure20261025a
open GammaConstantFormClosure20261026a
open GenericResolventScalarMeasure20261025a
open GenericResolventCyclicL2Representation20261025a
open GenericResolventCyclicIntertwining20261025a
open GenericResolventGlobalSpectralAssembly20261025a
open GenericCyclicBorelProjection20261025a
open GenericGlobalBorelProjection20261025a
open GenericGlobalProjectionScalarConsistency20261025a
open GenericResolventUnboundedScalarMeasure20261025a

section GenericFixedFiber
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (R : H →L[ℂ] H) (hSA : IsSelfAdjoint R)

def oneFiber : Set (ResolventSpectrum R) := {r | (r : ℝ) = 1}

theorem oneFiber_measurable : MeasurableSet (oneFiber R) :=
  (isClosed_eq continuous_subtype_val continuous_const).measurableSet

/-- Pointwise scalar multiplication, not an assumed spectral kernel law. -/
theorem fiber_coordinate_fixed_iff_oneIndicator (f : H) (a : ScalarL2 R hSA f) :
    coordinateMultiplier R hSA f a = a ↔
      borelMultiplier R hSA f (oneFiber R) (oneFiber_measurable R) a = a := by
  constructor
  · intro hfixed
    apply Lp.ext
    have hcoord := coordinateMultiplier_coe_ae R hSA f a
    rw [hfixed] at hcoord
    filter_upwards [hcoord, borelMultiplier_coe_ae R hSA f
      (oneFiber R) (oneFiber_measurable R) a] with r hr hB
    rw [hB]
    by_cases h1 : (r : ℝ) = 1
    · simp only [oneFiber, Set.mem_setOf_eq, h1, Set.indicator_of_mem]
    · have hc : ((r : ℝ) : ℂ) - 1 ≠ 0 := by
        intro hz
        apply h1
        exact Complex.ofReal_injective (sub_eq_zero.mp hz)
      have hz : (((r : ℝ) : ℂ) - 1) * a r = 0 := by
        linear_combination -hr
      have ha : a r = 0 := (mul_eq_zero.mp hz).resolve_left hc
      simp only [oneFiber, Set.mem_setOf_eq, h1, not_false_eq_true,
        Set.indicator_of_notMem, ha]
  · intro hfixed
    apply Lp.ext
    have hB := borelMultiplier_coe_ae R hSA f (oneFiber R) (oneFiber_measurable R) a
    rw [hfixed] at hB
    filter_upwards [hB, coordinateMultiplier_coe_ae R hSA f a] with r hr hcoord
    rw [hcoord]
    by_cases h1 : (r : ℝ) = 1
    · simp only [h1, Complex.ofReal_one, one_mul]
    · have ha : a r = 0 := by
        simpa only [oneFiber, Set.mem_setOf_eq, h1, not_false_eq_true,
          Set.indicator_of_notMem] using hr
      simp only [ha, mul_zero]

theorem diagonal_fixed_iff_oneIndicator (a : SpectralSum R hSA) :
    diagonalResolvent R hSA a = a ↔
      diagonalBorel R hSA (oneFiber R) (oneFiber_measurable R) a = a := by
  constructor
  · intro h
    apply lp.ext
    intro i
    exact (fiber_coordinate_fixed_iff_oneIndicator R hSA (i : H) (a i)).mp
      (congrArg (fun b : SpectralSum R hSA => b i) h)
  · intro h
    apply lp.ext
    intro i
    exact (fiber_coordinate_fixed_iff_oneIndicator R hSA (i : H) (a i)).mpr
      (congrArg (fun b : SpectralSum R hSA => b i) h)

/-- Actual global unitary transport of the proved scalar fixed-fiber law. -/
theorem resolvent_fixed_iff_oneProjection (u : H) :
    R u = u ↔ globalBorelProjection R hSA (oneFiber R) (oneFiber_measurable R) u = u := by
  let U := spectralUnitary R hSA
  let a := U.symm u
  constructor
  · intro h
    have hD : diagonalResolvent R hSA a = a := by
      apply U.injective
      simpa only [a, U.apply_symm_apply, h] using spectralUnitary_intertwine R hSA a
    have hB := (diagonal_fixed_iff_oneIndicator R hSA a).mp hD
    change U (diagonalBorel R hSA (oneFiber R) (oneFiber_measurable R) a) = u
    rw [hB]
    exact U.apply_symm_apply u
  · intro h
    have hB : diagonalBorel R hSA (oneFiber R) (oneFiber_measurable R) a = a := by
      apply U.injective
      simpa only [a, U.apply_symm_apply] using h
    have hD := (diagonal_fixed_iff_oneIndicator R hSA a).mpr hB
    calc
      R u = R (U a) := by rw [a, U.apply_symm_apply]
      _ = U (diagonalResolvent R hSA a) := (spectralUnitary_intertwine R hSA a).symm
      _ = u := by rw [hD]; exact U.apply_symm_apply u

/-- The inverse-coordinate convention used by the true unbounded scalar
measure has zero fiber exactly at r=1, including at the total value r=0. -/
theorem spectralLambda_preimage_zero :
    spectralLambda R ⁻¹' ({0} : Set ℝ) = oneFiber R := by
  ext r
  change ((r : ℝ)⁻¹ - 1 = 0) ↔ (r : ℝ) = 1
  constructor
  · intro h
    have hi : (r : ℝ)⁻¹ = 1 := sub_eq_zero.mp h
    have hinv := congrArg (fun x : ℝ => x⁻¹) hi
    simpa only [inv_inv, inv_one] using hinv
  · intro h
    simp only [h, inv_one, sub_self]
end GenericFixedFiber

/-- The actual lambda=0 Borel projection on the unchanged quotient L2. -/
def actualZeroProjection (N : ℕ) [NeZero N] : QuotientL2 N →L[ℂ] QuotientL2 N :=
  globalBorelProjection (actualGammaResolvent N) (actualGammaResolvent_selfAdjoint N)
    (oneFiber (actualGammaResolvent N)) (oneFiber_measurable (actualGammaResolvent N))

theorem kernel_mem_iff_resolvent_fixed (N : ℕ) [NeZero N] (u : QuotientL2 N) :
    u ∈ ambientFriedrichsKernel N ↔ actualGammaResolvent N u = u := by
  rw [ambientFriedrichsKernel_mem_iff, actualGammaFriedrichs_mem_graph_iff, add_zero]

/-- Full genuine unbounded lambda graph, rather than a bounded-R-only alias. -/
theorem kernel_mem_iff_actualLambdaGraph (N : ℕ) [NeZero N] (u : QuotientL2 N) :
    u ∈ ambientFriedrichsKernel N ↔
      actualGlobalFamilyLambdaGraph N (actualGlobalSpectralCoordinates N u) 0 := by
  rw [ambientFriedrichsKernel_mem_iff, actualGammaFriedrichs_global_graph_iff_lambda]
  simp only [actualGlobalSpectralCoordinates, map_zero]

theorem actualZeroProjection_fixed_iff_kernel (N : ℕ) [NeZero N] (u : QuotientL2 N) :
    actualZeroProjection N u = u ↔ u ∈ ambientFriedrichsKernel N := by
  rw [kernel_mem_iff_resolvent_fixed]
  exact (resolvent_fixed_iff_oneProjection (actualGammaResolvent N)
    (actualGammaResolvent_selfAdjoint N) u).symm

theorem actualZeroProjection_idempotent (N : ℕ) [NeZero N] (u : QuotientL2 N) :
    actualZeroProjection N (actualZeroProjection N u) = actualZeroProjection N u :=
  congrArg (fun T : QuotientL2 N →L[ℂ] QuotientL2 N => T u)
    (globalBorelProjection_idempotent (actualGammaResolvent N)
      (actualGammaResolvent_selfAdjoint N) _ _)

theorem actualZeroProjection_mem_kernel (N : ℕ) [NeZero N] (u : QuotientL2 N) :
    actualZeroProjection N u ∈ ambientFriedrichsKernel N :=
  (actualZeroProjection_fixed_iff_kernel N _).mp (actualZeroProjection_idempotent N u)

theorem actualKernel_isClosed (N : ℕ) [NeZero N] :
    IsClosed (ambientFriedrichsKernel N : Set (QuotientL2 N)) := by
  have heq : (ambientFriedrichsKernel N : Set (QuotientL2 N)) =
      {u | actualGammaResolvent N u = u} := by
    ext u
    exact kernel_mem_iff_resolvent_fixed N u
  rw [heq]
  exact isClosed_eq (actualGammaResolvent N).continuous continuous_id

local instance kernelComplete (N : ℕ) [NeZero N] : CompleteSpace (ambientFriedrichsKernel N) :=
  (actualKernel_isClosed N).completeSpace_coe

def actualKernelOrthogonalProjection (N : ℕ) [NeZero N] :
    QuotientL2 N →L[ℂ] QuotientL2 N := (ambientFriedrichsKernel N).starProjection

/-- Exact orthogonal projection identity, before any kernel classification. -/
theorem actualZeroProjection_eq_kernelOrthogonalProjection (N : ℕ) [NeZero N] :
    actualZeroProjection N = actualKernelOrthogonalProjection N := by
  ext u
  symm
  apply (ambientFriedrichsKernel N).eq_starProjection_of_mem_of_inner_eq_zero
    (actualZeroProjection_mem_kernel N u)
  intro w hw
  rw [inner_sub_left]
  have hsym := globalBorelProjection_inner (actualGammaResolvent N)
    (actualGammaResolvent_selfAdjoint N) (oneFiber (actualGammaResolvent N))
    (oneFiber_measurable (actualGammaResolvent N)) u w
  change inner ℂ (actualZeroProjection N u) w = inner ℂ u (actualZeroProjection N w) at hsym
  rw [(actualZeroProjection_fixed_iff_kernel N w).mpr hw] at hsym
  rw [hsym, sub_self]

/-- The actual unbounded scalar measure keeps its true lambda=0 atom:
it is exactly the physical squared norm of the actual kernel projection. -/
theorem actualLaplaceMeasure_zero_eq_projection_norm_sq (N : ℕ) [NeZero N]
    (u : QuotientL2 N) : actualLaplaceMeasure N u {0} =
      ENNReal.ofReal (‖actualZeroProjection N u‖ ^ 2) := by
  change ((scalarMeasure (actualGammaResolvent N) (actualGammaResolvent_selfAdjoint N) u).map
    (spectralLambda (actualGammaResolvent N))) {0} = _
  rw [Measure.map_apply (measurable_spectralLambda (actualGammaResolvent N))
    measurableSet_singleton, spectralLambda_preimage_zero]
  exact scalarMeasure_eq_projection_norm_square (actualGammaResolvent N)
    (actualGammaResolvent_selfAdjoint N) u _ _

end
end ImbalancedChen.Part3.GammaZeroSpectralProjectionKernel20261026a

