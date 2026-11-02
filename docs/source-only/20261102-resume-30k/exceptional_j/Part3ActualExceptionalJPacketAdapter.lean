import ImbalancedChen.Part3ActualExceptionalJSmallKernel
import ImbalancedChen.Part3ActualCommonHeightKFactorizationFullGram
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Tactic

/-!
# The positive-sign J transform of the unchanged physical packet

Source-only K candidate. Only the continuous q-kernel is replaced. The
original normalizedF, rho, Y0, signed cusp phase, all finite row/n labels,
one m interval, and one common additive phase remain literally the same.
Both physical and Fourier-mode equalities are proved. Existing exact
Fourier reconstruction then gives a genuine HasSum for this J source.
No automorphic Fourier coefficients or spectral source dictionary are
manufactured from this finite smooth packet.
-/

namespace ImbalancedChen.Part3.ActualExceptionalJPacketAdapter20261102

noncomputable section
open Classical Set MeasureTheory
open scoped BigOperators
open P3ActualLiteralPacketIntegralSourceOnly
open P3NativePeriod64SamplingSourceOnly (D4)
open P3Period64NativeReconstructionSourceOnly
  (point4 actualCoeff spectralTest spectralMode chi chi_mul_actual)
open ActualNormalizedSmoothF (normalizedF)
open ActualCommonHeightKGramSourceOnly (completedPacketSum)
open ActualExceptionalJSmallKernel20261102

variable {ι : Type*}

def halfLinePositiveKernel (a : ℝ) (ha : 0 < a) (alpha : ℝ)
    (ha0 : 0 ≤ alpha) (halpha : alpha ≤ exceptionalCap) : C(Ici a, ℂ) where
  toFun q := positiveSignKernel alpha (q : ℝ) / ((q : ℝ) : ℂ)
  continuous_toFun := by
    apply continuous_iff_continuousAt.mpr
    intro q
    have hq : 0 < (q : ℝ) := ha.trans_le q.property
    exact ((positiveSignKernel_continuousAt ha0 halpha hq).comp
      continuous_subtype_val.continuousAt).div
        (by fun_prop) (Complex.ofReal_ne_zero.mpr hq.ne')

def extendedPositiveKernel (a : ℝ) (ha : 0 < a) (alpha : ℝ)
    (ha0 : 0 ≤ alpha) (halpha : alpha ≤ exceptionalCap) : C(ℝ, ℂ) :=
  extendKernelFromHalfLine a (halfLinePositiveKernel a ha alpha ha0 halpha)

theorem extendedPositiveKernel_eq (a : ℝ) (ha : 0 < a)
    (alpha q : ℝ) (ha0 : 0 ≤ alpha) (halpha : alpha ≤ exceptionalCap) (hq : a ≤ q) :
    extendedPositiveKernel a ha alpha ha0 halpha q =
      positiveSignKernel alpha q / (q : ℂ) := by
  exact extendKernelFromHalfLine_eq a (halfLinePositiveKernel a ha alpha ha0 halpha) q hq

theorem extendedPositiveKernel_eq_on_region (P : PacketData ι)
    (alpha q : ℝ) (ha0 : 0 ≤ alpha) (halpha : alpha ≤ exceptionalCap) (hq : q ∈ P.region) :
    extendedPositiveKernel (P.Y0 / 32) (by have h := P.Y0_pos; positivity)
      alpha ha0 halpha q = positiveSignKernel alpha q / (q : ℂ) := by
  apply extendedPositiveKernel_eq
  change P.Y0 / 16 ≤ q ∧ q ≤ 16 * P.Y0 at hq
  linarith [P.Y0_pos]

/-- Exactly the original PacketData with a common normalized positive J/q
kernel; no carriers, coefficient, cusp sign, scale or phase is changed. -/
def withPositiveKernel (P : PacketData ι) (alpha : ℝ)
    (ha0 : 0 ≤ alpha) (halpha : alpha ≤ exceptionalCap) : PacketData ι :=
  { P with kernel := fun _ _ _ =>
      extendedPositiveKernel (P.Y0 / 32) (by have h := P.Y0_pos; positivity)
        alpha ha0 halpha }

def positivePhysical (P : PacketData ι) (alpha q : ℝ) : ℂ :=
  ∑ j ∈ P.rows, ∑ m ∈ P.mCarrier, ∑ n ∈ P.nCarrier j,
    signedCoefficient P.negativeCusp (P.packet j) n *
      (positiveSignKernel alpha q / (q : ℂ)) *
      normalizedF P.rho P.sigma
        (point4 (q / P.Y0) ((m : ℝ) / P.V)
          ((((P.packet j).multiplier * n : ℕ) : ℝ) / P.U)
          (((P.packet j).level : ℝ) / P.Z))

def positiveModeFunction (P : PacketData ι) (k : D4 → ℤ) (alpha q : ℝ) : ℂ :=
  spectralTest k P.Y0 q *
    (∑ j ∈ P.rows, ∑ m ∈ P.mCarrier, ∑ n ∈ P.nCarrier j,
      (P.completed k).weight m *
        signedCoefficient P.negativeCusp (modePacket (P.packet j) k P.U P.Z) n *
          (positiveSignKernel alpha q / (q : ℂ)))

def positiveSignTestTransform (P : PacketData ι) (k : D4 → ℤ) (alpha : ℝ) : ℂ :=
  ∫ q : ℝ, spectralTest k P.Y0 q * (positiveSignKernel alpha q / (q : ℂ))

private theorem positivePhysical_zero_off (P : PacketData ι)
    (alpha q : ℝ) (hq : q ∉ P.region) : positivePhysical P alpha q = 0 := by
  have hF (v w z : ℝ) :
      normalizedF P.rho P.sigma (point4 (q / P.Y0) v w z) = 0 := by
    have hh := chi_mul_actual P.rho P.sigma (point4 (q / P.Y0) v w z)
    change (chi (q / P.Y0) : ℂ) *
      normalizedF P.rho P.sigma (point4 (q / P.Y0) v w z) =
        normalizedF P.rho P.sigma (point4 (q / P.Y0) v w z) at hh
    rw [P.chi_scaled_zero_off q hq] at hh
    simpa only [Complex.ofReal_zero, zero_mul] using hh.symm
  simp only [positivePhysical, hF, mul_zero, Finset.sum_const_zero]

theorem withPositiveKernel_physical (P : PacketData ι) (alpha : ℝ)
    (ha0 : 0 ≤ alpha) (halpha : alpha ≤ exceptionalCap) :
    (withPositiveKernel P alpha ha0 halpha).physical = positivePhysical P alpha := by
  funext q
  by_cases hq : q ∈ P.region
  · change
      (∑ j ∈ P.rows, ∑ m ∈ P.mCarrier, ∑ n ∈ P.nCarrier j,
        signedCoefficient P.negativeCusp (P.packet j) n *
          extendedPositiveKernel (P.Y0 / 32) (by have h := P.Y0_pos; positivity)
            alpha ha0 halpha q *
          normalizedF P.rho P.sigma
            (point4 (q / P.Y0) ((m : ℝ) / P.V)
              ((((P.packet j).multiplier * n : ℕ) : ℝ) / P.U)
              (((P.packet j).level : ℝ) / P.Z))) = positivePhysical P alpha q
    unfold positivePhysical
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro m _
    apply Finset.sum_congr rfl
    intro n _
    rw [extendedPositiveKernel_eq_on_region P alpha q ha0 halpha hq]
  · rw [(withPositiveKernel P alpha ha0 halpha).physical_zero_off q hq,
      positivePhysical_zero_off P alpha q hq]

theorem withPositiveKernel_modeFunction (P : PacketData ι) (k : D4 → ℤ) (alpha : ℝ)
    (ha0 : 0 ≤ alpha) (halpha : alpha ≤ exceptionalCap) :
    (withPositiveKernel P alpha ha0 halpha).modeFunction k =
      positiveModeFunction P k alpha := by
  funext q
  change spectralTest k P.Y0 q *
    (∑ j ∈ P.rows, ∑ m ∈ P.mCarrier, ∑ n ∈ P.nCarrier j,
      (P.completed k).weight m *
        signedCoefficient P.negativeCusp (modePacket (P.packet j) k P.U P.Z) n *
          extendedPositiveKernel (P.Y0 / 32) (by have h := P.Y0_pos; positivity)
            alpha ha0 halpha q) = positiveModeFunction P k alpha q
  unfold positiveModeFunction
  by_cases hq : q ∈ P.region
  · rw [extendedPositiveKernel_eq_on_region P alpha q ha0 halpha hq]
  · simp only [spectralTest, spectralMode, P.chi_scaled_zero_off q hq,
      Complex.ofReal_zero, zero_mul]

theorem positivePhysical_integrable (P : PacketData ι) (alpha : ℝ)
    (ha0 : 0 ≤ alpha) (halpha : alpha ≤ exceptionalCap) :
    Integrable (positivePhysical P alpha) := by
  rw [← withPositiveKernel_physical P alpha ha0 halpha]
  exact (withPositiveKernel P alpha ha0 halpha).physical_integrable

theorem positiveSignTestTransform_integrable (P : PacketData ι) (k : D4 → ℤ) (alpha : ℝ)
    (ha0 : 0 ≤ alpha) (halpha : alpha ≤ exceptionalCap) :
    Integrable (fun q : ℝ => spectralTest k P.Y0 q *
      (positiveSignKernel alpha q / (q : ℂ))) := by
  let K : C(ℝ, ℂ) := extendedPositiveKernel (P.Y0 / 32)
    (by have h := P.Y0_pos; positivity) alpha ha0 halpha
  have hc : Continuous (fun q : ℝ => spectralTest k P.Y0 q * K q) :=
    (P3Period64NativeReconstructionSourceOnly.spectralTest_contDiff k P.Y0).continuous.mul
      K.continuous
  have hi : Integrable (fun q : ℝ => spectralTest k P.Y0 q * K q) := by
    apply hc.integrable_of_hasCompactSupport
    apply (isCompact_Icc : IsCompact P.region).of_isClosed_subset isClosed_closure
    apply closure_minimal _ (isClosed_Icc : IsClosed P.region)
    intro q hq
    by_contra hn
    apply hq
    simp only [spectralTest, spectralMode, P.chi_scaled_zero_off q hn,
      Complex.ofReal_zero, zero_mul]
  have he : (fun q : ℝ => spectralTest k P.Y0 q * K q) =
      (fun q : ℝ => spectralTest k P.Y0 q * (positiveSignKernel alpha q / (q : ℂ))) := by
    funext q
    by_cases hq : q ∈ P.region
    · change spectralTest k P.Y0 q * extendedPositiveKernel (P.Y0 / 32)
        (by have h := P.Y0_pos; positivity) alpha ha0 halpha q = _
      rw [extendedPositiveKernel_eq_on_region P alpha q ha0 halpha hq]
    · simp only [spectralTest, spectralMode, P.chi_scaled_zero_off q hq,
        Complex.ofReal_zero, zero_mul]
  rw [← he]
  exact hi

theorem positive_mode_factorization (P : PacketData ι) (k : D4 → ℤ) (alpha q : ℝ) :
    positiveModeFunction P k alpha q =
      (spectralTest k P.Y0 q * (positiveSignKernel alpha q / (q : ℂ))) *
        completedPacketSum P k := by
  unfold positiveModeFunction completedPacketSum
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro m _
  apply Finset.sum_congr rfl
  intro n _
  ring

theorem positive_modeIntegral (P : PacketData ι) (k : D4 → ℤ) (alpha : ℝ) :
    (∫ q : ℝ, positiveModeFunction P k alpha q) =
      positiveSignTestTransform P k alpha * completedPacketSum P k := by
  calc
    _ = ∫ q : ℝ, (spectralTest k P.Y0 q *
        (positiveSignKernel alpha q / (q : ℂ))) * completedPacketSum P k := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun q => positive_mode_factorization P k alpha q)
    _ = _ := integral_mul_const (completedPacketSum P k) _

/-- Exact reconstruction for the actual positive J physical source. This
is an analytic HasSum, not a finite-mode truncation assertion. -/
theorem positivePhysical_hasSum (P : PacketData ι) (alpha : ℝ)
    (ha0 : 0 ≤ alpha) (halpha : alpha ≤ exceptionalCap) :
    HasSum (fun k : D4 → ℤ => actualCoeff P.rho P.sigma k *
      (positiveSignTestTransform P k alpha * completedPacketSum P k))
        (∫ q : ℝ, positivePhysical P alpha q) := by
  have h := (withPositiveKernel P alpha ha0 halpha).hasSum_coefficient_times_modeIntegral 0
  rw [withPositiveKernel_physical] at h
  apply h.congr_fun
  intro k
  change actualCoeff P.rho P.sigma k *
    (∫ q : ℝ, (withPositiveKernel P alpha ha0 halpha).modeFunction k q) = _
  rw [withPositiveKernel_modeFunction, positive_modeIntegral]

end
end ImbalancedChen.Part3.ActualExceptionalJPacketAdapter20261102
