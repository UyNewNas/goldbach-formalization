import ImbalancedChen.Part3ImaginaryOrderKExplicitMajorant
import ImbalancedChen.Part3ActualCommonHeightKFactorizationFullGram

/-!
SOURCEONLY / UNCOMPILED / no acceptance credit. 2026-10-24.
Public compact-q and common-height adapters for the actual K integral.
The compact interval is fixed independently of spectral height. The
normalization K_{2it}(q)/q, frozen completed sum, and original Fourier
coefficient are retained. Every bound below is absolute and uniform in t;
none supplies spectral decay or a Kuznetsov/Plancherel identification.
-/

namespace ImbalancedChen.Part3.P0MajorantPublicAPISourceOnly
noncomputable section

open Set MeasureTheory
open scoped Topology BigOperators
open P3ActualLiteralPacketIntegralSourceOnly
open P3NativePeriod64SamplingSourceOnly (D4)
open P3Period64NativeReconstructionSourceOnly
  (actualCoeff spectralTest spectralMode)
open ImaginaryOrderKBesselSourceOnly
open ImaginaryOrderKExplicitMajorantSourceOnly
open ActualKPacketAdapterSourceOnly
open ActualCommonHeightKGramSourceOnly

variable {ι : Type*}

/-- The literal K/q kernel on a fixed positive compact q interval.
The extension is used only to construct the continuous-map object. -/
def compactQKernel (a b : ℝ) (ha : 0 < a) (t : ℝ) : C(Icc a b, ℂ) :=
  (extendedKKernel a ha t).comp ⟨Subtype.val, continuous_subtype_val⟩

theorem compactQKernel_apply (a b : ℝ) (ha : 0 < a) (t : ℝ)
    (q : Icc a b) :
    compactQKernel a b ha t q =
      (imaginaryOrderK t (q : ℝ) : ℂ)/((q : ℝ) : ℂ) := by
  change extendedKKernel a ha t (q : ℝ) = _
  exact extendedKKernel_eq a ha t (q : ℝ) q.property.1

/-- Lower-endpoint majorant, with no upper-endpoint or height dependence. -/
theorem kQuotient_norm_le_of_lower (t : ℝ) {a q : ℝ}
    (ha : 0 < a) (haq : a ≤ q) :
    ‖(imaginaryOrderK t q : ℂ)/(q : ℂ)‖ ≤ 2/a^2 := by
  have hq : 0 < q := lt_of_lt_of_le ha haq
  calc
    ‖(imaginaryOrderK t q : ℂ)/(q : ℂ)‖ ≤ 2/q^2 :=
      imaginaryOrderK_div_norm_le t hq
    _ ≤ 2/a^2 := by
      gcongr <;> linarith

/-- This is the continuous-map sup norm of a concrete kernel. -/
theorem compactQKernel_norm_le (a b : ℝ) (ha : 0 < a) (t : ℝ) :
    ‖compactQKernel a b ha t‖ ≤ 2/a^2 := by
  apply (ContinuousMap.norm_le _ (by positivity : (0 : ℝ) ≤ 2/a^2)).mpr
  intro q
  rw [compactQKernel_apply]
  exact kQuotient_norm_le_of_lower t ha q.property.1

/-- The public physical compact kernel is the previously defined restriction. -/
theorem compactQKernel_eq_restricted (P : PacketData ι) (t : ℝ) :
    compactQKernel (P.Y0/16) (16*P.Y0)
        (by have h := P.Y0_pos; positivity) t =
      restrictedKKernel P t := by
  ext q
  rw [compactQKernel_apply, restrictedKKernel_eq]

/-- Exact evenness survives compact restriction. -/
theorem compactQKernel_neg (a b : ℝ) (ha : 0 < a) (t : ℝ) :
    compactQKernel a b ha (-t) = compactQKernel a b ha t := by
  ext q
  rw [compactQKernel_apply, compactQKernel_apply, imaginaryOrderK_neg]

theorem spectralTest_zero_off_region (P : PacketData ι)
    (k : D4 → ℤ) (q : ℝ) (hq : q ∉ P.region) :
    spectralTest k P.Y0 q = 0 := by
  simp only [spectralTest, spectralMode, P.chi_scaled_zero_off q hq,
    Complex.ofReal_zero, zero_mul]

/-- Integrability is proved for the actual compactly supported test. -/
theorem spectralTest_integrable (P : PacketData ι) (k : D4 → ℤ) :
    Integrable (spectralTest k P.Y0) := by
  have hc : Continuous (spectralTest k P.Y0) :=
    (P3Period64NativeReconstructionSourceOnly.spectralTest_contDiff k P.Y0).continuous
  apply hc.integrable_of_hasCompactSupport
  apply (isCompact_Icc : IsCompact P.region).of_isClosed_subset isClosed_closure
  apply closure_minimal _ (isClosed_Icc : IsClosed P.region)
  intro q hq
  by_contra hn
  exact hq (spectralTest_zero_off_region P k q hn)

/-- L1 mass of the actual test used in the existing factorization. -/
def testL1Mass (P : PacketData ι) (k : D4 → ℤ) : ℝ :=
  ∫ q : ℝ, ‖spectralTest k P.Y0 q‖

theorem testL1Mass_nonneg (P : PacketData ι) (k : D4 → ℤ) :
    0 ≤ testL1Mass P k := by
  exact integral_nonneg (fun _ => norm_nonneg _)

/-- Global pointwise domination uses the actual test's vanishing off support. -/
theorem testK_norm_le (P : PacketData ι) (k : D4 → ℤ) (t q : ℝ) :
    ‖spectralTest k P.Y0 q * ((imaginaryOrderK t q : ℂ)/(q : ℂ))‖ ≤
      ‖spectralTest k P.Y0 q‖ * (512/P.Y0^2) := by
  by_cases hq : q ∈ P.region
  · have hK : ‖(imaginaryOrderK t q : ℂ)/(q : ℂ)‖ ≤ 512/P.Y0^2 := by
      rw [← extendedKKernel_eq_on_physical_region P t q hq]
      exact extendedKKernel_norm_le_on_region P t q hq
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left hK (norm_nonneg _)
  · rw [spectralTest_zero_off_region P k q hq]
    simp

/-- A proved, finite, height-uniform bound on the exact K test transform. -/
theorem kTestTransform_norm_le (P : PacketData ι) (k : D4 → ℤ) (t : ℝ) :
    ‖kTestTransform P k t‖ ≤ testL1Mass P k * (512/P.Y0^2) := by
  calc
    ‖kTestTransform P k t‖ ≤
        ∫ q : ℝ, ‖spectralTest k P.Y0 q‖ * (512/P.Y0^2) := by
      exact norm_integral_le_of_norm_le
        ((spectralTest_integrable P k).norm.mul_const (512/P.Y0^2))
        (Filter.Eventually.of_forall (testK_norm_le P k t))
    _ = testL1Mass P k * (512/P.Y0^2) :=
      integral_mul_const (512/P.Y0^2) _

/-- Exact common-height packet factorization followed by its absolute bound.
The coefficient sum is the actual frozen completedPacketSum, not a premise. -/
theorem commonHeight_modeIntegral_norm_le (P : PacketData ι)
    (k : D4 → ℤ) (t : ℝ) :
    ‖∫ q : ℝ, kModeFunction P (commonHeight t) k q‖ ≤
      testL1Mass P k * (512/P.Y0^2) * ‖completedPacketSum P k‖ := by
  rw [actual_common_height_modeIntegral, norm_mul]
  exact mul_le_mul_of_nonneg_right (kTestTransform_norm_le P k t) (norm_nonneg _)

/-- Energy form of the same bound, preserving the exact coefficient factor. -/
theorem commonHeight_modeIntegral_norm_sq_le (P : PacketData ι)
    (k : D4 → ℤ) (t : ℝ) :
    ‖∫ q : ℝ, kModeFunction P (commonHeight t) k q‖^2 ≤
      (testL1Mass P k * (512/P.Y0^2))^2 * ‖completedPacketSum P k‖^2 := by
  have h := kTestTransform_norm_le P k t
  have hnonneg : 0 ≤ testL1Mass P k * (512/P.Y0^2) :=
    mul_nonneg (testL1Mass_nonneg P k) (by positivity)
  have hsq : ‖kTestTransform P k t‖^2 ≤
      (testL1Mass P k * (512/P.Y0^2))^2 := by
    simpa only [pow_two] using mul_le_mul h h (norm_nonneg _) hnonneg
  rw [actual_common_height_modeIntegral_norm_sq]
  exact mul_le_mul_of_nonneg_right hsq (sq_nonneg _)

/-- The actual coefficient-weighted reconstruction now exposes the separated
K transform. This is the existing HasSum, without a new convergence premise. -/
theorem commonHeight_hasSum_factorized (P : PacketData ι) (t : ℝ) (J0 : ℕ) :
    HasSum (fun k : D4 → ℤ => actualCoeff P.rho P.sigma k *
      (kTestTransform P k t * completedPacketSum P k))
      (∫ q : ℝ, kPhysical P (commonHeight t) q) := by
  have h := k_hasSum_coefficient_times_modeIntegral P (commonHeight t) J0
  simpa only [actual_common_height_modeIntegral] using h

end
end ImbalancedChen.Part3.P0MajorantPublicAPISourceOnly
