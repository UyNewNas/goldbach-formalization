import ImbalancedChen.Part3ActualCommonHeightKFactorizationFullGram
import Mathlib.Tactic

/-!
SOURCEONLY / UNCOMPILED / 20261024z-P0. No acceptance credit.
Public adapters for the actual K/q packet, with all finite labels retained.
No height decay, majorant, spectral inequality, or Kuznetsov normalization
is assumed or proved here. In particular c below is an explicitly supplied
scalar, not an assertion that a missing spectral normalization equals c.
-/

namespace ImbalancedChen.Part3.P0PacketPublicAPISourceOnly
noncomputable section

open Set MeasureTheory
open scoped BigOperators
open P3ActualLiteralPacketIntegralSourceOnly
open P3NativePeriod64SamplingSourceOnly (D4)
open P3Period64NativeReconstructionSourceOnly (actualCoeff)
open ImaginaryOrderKBesselSourceOnly
open ActualKPacketAdapterSourceOnly
open ActualCommonHeightKGramSourceOnly

variable {ι : Type*}

/-- Evenness of the actual defining u integral also permits absolute height. -/
theorem imaginaryOrderK_abs (t q : ℝ) :
    imaginaryOrderK |t| q = imaginaryOrderK t q := by
  by_cases ht : 0 ≤ t
  · rw [abs_of_nonneg ht]
  · rw [abs_of_neg (lt_of_not_ge ht), imaginaryOrderK_neg]

/-- A parameter is used only on the original finite packet carriers.
An independent sign can be chosen at every original (j,m,n) label. -/
theorem kPhysical_congr_signed_on_carriers (P : PacketData ι)
    (s t : ι → ℕ → ℕ → ℝ)
    (hst : ∀ j ∈ P.rows, ∀ m ∈ P.mCarrier, ∀ n ∈ P.nCarrier j,
      s j m n = t j m n ∨ s j m n = -(t j m n)) :
    kPhysical P s = kPhysical P t := by
  funext q
  unfold kPhysical
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro m hm
  apply Finset.sum_congr rfl
  intro n hn
  rcases hst j hj m hm n hn with he | he
  · rw [he]
  · rw [he, imaginaryOrderK_neg]

theorem kModeFunction_congr_signed_on_carriers (P : PacketData ι)
    (s t : ι → ℕ → ℕ → ℝ)
    (hst : ∀ j ∈ P.rows, ∀ m ∈ P.mCarrier, ∀ n ∈ P.nCarrier j,
      s j m n = t j m n ∨ s j m n = -(t j m n))
    (k : D4 → ℤ) : kModeFunction P s k = kModeFunction P t k := by
  funext q
  unfold kModeFunction
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro m hm
  apply Finset.sum_congr rfl
  intro n hn
  rcases hst j hj m hm n hn with he | he
  · rw [he]
  · rw [he, imaginaryOrderK_neg]

theorem kPhysical_neg (P : PacketData ι) (t : ι → ℕ → ℕ → ℝ) :
    kPhysical P (fun j m n => -(t j m n)) = kPhysical P t := by
  funext q
  simp only [kPhysical, imaginaryOrderK_neg]

theorem kModeFunction_neg (P : PacketData ι) (t : ι → ℕ → ℕ → ℝ)
    (k : D4 → ℤ) :
    kModeFunction P (fun j m n => -(t j m n)) k = kModeFunction P t k := by
  funext q
  simp only [kModeFunction, imaginaryOrderK_neg]

theorem kPhysical_abs (P : PacketData ι) (t : ι → ℕ → ℕ → ℝ) :
    kPhysical P (fun j m n => |t j m n|) = kPhysical P t := by
  funext q
  simp only [kPhysical, imaginaryOrderK_abs]

theorem kModeFunction_abs (P : PacketData ι) (t : ι → ℕ → ℕ → ℝ)
    (k : D4 → ℤ) :
    kModeFunction P (fun j m n => |t j m n|) k = kModeFunction P t k := by
  funext q
  simp only [kModeFunction, imaginaryOrderK_abs]

theorem kTestTransform_neg (P : PacketData ι) (k : D4 → ℤ) (t : ℝ) :
    kTestTransform P k (-t) = kTestTransform P k t := by
  simp only [kTestTransform, imaginaryOrderK_neg]

theorem kTestTransform_abs (P : PacketData ι) (k : D4 → ℤ) (t : ℝ) :
    kTestTransform P k |t| = kTestTransform P k t := by
  simp only [kTestTransform, imaginaryOrderK_abs]

/-- Direct public consumer of reconstruction at a single common height. -/
theorem commonHeight_hasSum_transform_times_packet (P : PacketData ι)
    (t : ℝ) (J0 : ℕ) :
    HasSum (fun k : D4 → ℤ => actualCoeff P.rho P.sigma k *
      (kTestTransform P k t * completedPacketSum P k))
      (∫ q : ℝ, kPhysical P (commonHeight t) q) := by
  simpa only [actual_common_height_modeIntegral] using
    k_hasSum_coefficient_times_modeIntegral P (commonHeight t) J0

/-- Rowwise sign choices specialize to the SAME common-height transform;
the scalar transform is not replaced by an absolute-value majorant. -/
theorem signed_commonHeight_modeIntegral (P : PacketData ι)
    (s : ι → ℕ → ℕ → ℝ) (t : ℝ)
    (hst : ∀ j ∈ P.rows, ∀ m ∈ P.mCarrier, ∀ n ∈ P.nCarrier j,
      s j m n = t ∨ s j m n = -t) (k : D4 → ℤ) :
    (∫ q : ℝ, kModeFunction P s k q) =
      kTestTransform P k t * completedPacketSum P k := by
  have he := kModeFunction_congr_signed_on_carriers P s (commonHeight t) hst k
  rw [he, actual_common_height_modeIntegral]

/-- Concrete scalar normalization of the continuous actual K/q kernel.
Every packet field other than kernel is inherited from the original P. -/
def withScalarKKernel (P : PacketData ι) (t : ι → ℕ → ℕ → ℝ)
    (c : ℂ) : PacketData ι :=
  { withKKernel P t with
    kernel := fun j m n => c • (withKKernel P t).kernel j m n }

theorem withScalarKKernel_frozen (P : PacketData ι)
    (t : ι → ℕ → ℕ → ℝ) (c : ℂ) :
    (withScalarKKernel P t c).rows = P.rows ∧
    (withScalarKKernel P t c).packet = P.packet ∧
    (withScalarKKernel P t c).nCarrier = P.nCarrier ∧
    (withScalarKKernel P t c).mCarrier = P.mCarrier ∧
    (withScalarKKernel P t c).completed = P.completed ∧
    (withScalarKKernel P t c).region = P.region ∧
    (withScalarKKernel P t c).rho = P.rho ∧
    (withScalarKKernel P t c).sigma = P.sigma ∧
    (withScalarKKernel P t c).negativeCusp = P.negativeCusp ∧
    (withScalarKKernel P t c).Y0 = P.Y0 ∧
    (withScalarKKernel P t c).V = P.V ∧
    (withScalarKKernel P t c).U = P.U ∧
    (withScalarKKernel P t c).Z = P.Z := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem withScalarKKernel_physical (P : PacketData ι)
    (t : ι → ℕ → ℕ → ℝ) (c : ℂ) :
    (withScalarKKernel P t c).physical = fun q => c * kPhysical P t q := by
  rw [← withKKernel_physical P t]
  funext q
  unfold withScalarKKernel PacketData.physical
  simp only [ContinuousMap.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _hj
  apply Finset.sum_congr rfl
  intro m _hm
  apply Finset.sum_congr rfl
  intro n _hn
  ring

theorem withScalarKKernel_modeFunction (P : PacketData ι)
    (t : ι → ℕ → ℕ → ℝ) (c : ℂ) (k : D4 → ℤ) :
    (withScalarKKernel P t c).modeFunction k =
      fun q => c * kModeFunction P t k q := by
  rw [← withKKernel_modeFunction P t k]
  funext q
  unfold withScalarKKernel PacketData.modeFunction PacketData.modeCore
  simp only [ContinuousMap.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _hj
  apply Finset.sum_congr rfl
  intro m _hm
  apply Finset.sum_congr rfl
  intro n _hn
  ring

/-- Pointwise normalizer on the actual physical region, preserving dq/q. -/
theorem withScalarKKernel_kernel_on_region (P : PacketData ι)
    (t : ι → ℕ → ℕ → ℝ) (c : ℂ) (j : ι) (m n : ℕ)
    (q : ℝ) (hq : q ∈ P.region) :
    (withScalarKKernel P t c).kernel j m n q =
      c * ((imaginaryOrderK (t j m n) q : ℂ)/(q : ℂ)) := by
  change (c • extendedKKernel (P.Y0/32)
    (by have h := P.Y0_pos; positivity) (t j m n)) q = _
  rw [ContinuousMap.smul_apply, smul_eq_mul,
    extendedKKernel_eq_on_physical_region P (t j m n) q hq]

theorem scalar_kPhysical_integrable (P : PacketData ι)
    (t : ι → ℕ → ℕ → ℝ) (c : ℂ) :
    Integrable (fun q => c * kPhysical P t q) := by
  exact (kPhysical_integrable P t).const_mul c

theorem scalar_kModeFunction_integrable (P : PacketData ι)
    (t : ι → ℕ → ℕ → ℝ) (c : ℂ) (k : D4 → ℤ) :
    Integrable (fun q => c * kModeFunction P t k q) := by
  exact (kModeFunction_integrable P t k).const_mul c

theorem withScalarKKernel_physicalIntegral (P : PacketData ι)
    (t : ι → ℕ → ℕ → ℝ) (c : ℂ) :
    (∫ q : ℝ, (withScalarKKernel P t c).physical q) =
      c * ∫ q : ℝ, kPhysical P t q := by
  rw [withScalarKKernel_physical, integral_const_mul]

theorem withScalarKKernel_modeIntegral (P : PacketData ι)
    (t : ι → ℕ → ℕ → ℝ) (c : ℂ) (k : D4 → ℤ) :
    (∫ q : ℝ, (withScalarKKernel P t c).modeFunction k q) =
      c * ∫ q : ℝ, kModeFunction P t k q := by
  rw [withScalarKKernel_modeFunction, integral_const_mul]

/-- Exact normalized reconstruction from an actual PacketData record.
No change of Fourier coefficient, carrier, physical scale, or cutoff. -/
theorem scalar_hasSum_coefficient_times_modeIntegral (P : PacketData ι)
    (t : ι → ℕ → ℕ → ℝ) (c : ℂ) (J0 : ℕ) :
    HasSum (fun k : D4 → ℤ => actualCoeff P.rho P.sigma k *
      (c * ∫ q : ℝ, kModeFunction P t k q))
      (c * ∫ q : ℝ, kPhysical P t q) := by
  have h := (withScalarKKernel P t c).hasSum_coefficient_times_modeIntegral J0
  change HasSum (fun k : D4 → ℤ => actualCoeff P.rho P.sigma k *
    ∫ q : ℝ, (withScalarKKernel P t c).modeFunction k q)
    (∫ q : ℝ, (withScalarKKernel P t c).physical q) at h
  simpa only [withScalarKKernel_modeIntegral, withScalarKKernel_physicalIntegral] using h

theorem scalar_commonHeight_modeIntegral (P : PacketData ι)
    (c : ℂ) (k : D4 → ℤ) (t : ℝ) :
    (∫ q : ℝ, (withScalarKKernel P (commonHeight t) c).modeFunction k q) =
      (c * kTestTransform P k t) * completedPacketSum P k := by
  rw [withScalarKKernel_modeIntegral, actual_common_height_modeIntegral]
  ring

theorem scalar_commonHeight_modeIntegral_norm_sq (P : PacketData ι)
    (c : ℂ) (k : D4 → ℤ) (t : ℝ) :
    ‖∫ q : ℝ, (withScalarKKernel P (commonHeight t) c).modeFunction k q‖^2 =
      ‖c‖^2 * ‖kTestTransform P k t‖^2 * ‖completedPacketSum P k‖^2 := by
  rw [scalar_commonHeight_modeIntegral, norm_mul, norm_mul, mul_pow, mul_pow]

end
end ImbalancedChen.Part3.P0PacketPublicAPISourceOnly
