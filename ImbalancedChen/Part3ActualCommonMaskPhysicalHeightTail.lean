import ImbalancedChen.Part3ActualCommonMaskLongslotEnergy
import ImbalancedChen.P0HeightPublicAPI
import ImbalancedChen.P0P3RawHeightTail
import ImbalancedChen.P0P3SymmetricRawTail
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNCOMPILED, 2026-10-24.

True raw spectral-height decay for the *entire* physical PacketData with one
common m mask. The root actual imaginary-order K/q theorem supplies t^-2;
the already derived literal full-packet q-integral bound carries every row,
signed/coprime n coefficient, common m copy and normalized physical test.
Integrating t^-4 gives T^-3 on {|t| >= T}. This is Lebesgue dt, not a
Kuznetsov or automorphic spectral density.
-/

namespace ImbalancedChen.Part3.ActualCommonMaskPhysicalHeightTailSourceOnly
noncomputable section

open Classical Set MeasureTheory Filter
open scoped BigOperators
open P3ActualLiteralPacketIntegralSourceOnly
open P3ActualWeightedSpectralBudgetSourceOnly (actualW actualW_nonneg)
open ImaginaryOrderKBesselSourceOnly
open ActualKPacketAdapterSourceOnly
open ImbalancedChen.Part3.ActualCommonHeightKGramSourceOnly
open ImbalancedChen.Part3.ActualCommonMaskSourceOnly
open ImbalancedChen.Part3.ActualCommonMaskLongslotEnergySourceOnly
open ImbalancedChen.Part3.P0HeightPublicAPISourceOnly
open ImbalancedChen.Part3.P0P3RawHeightTailSourceOnly
open ImbalancedChen.Part3.P0P3SymmetricRawTailSourceOnly

variable {ι : Type*}

/-- Exact actual finite-packet coefficient in the height-decay majorant. -/
def physicalTailConstant (P : PacketData ι) (a b J0 : ℕ) : ℝ :=
  actualW P.rho P.sigma J0 * commonMaskCoefficientMass P a b *
    (2560/P.Y0^2) * ((255/16 : ℝ)*P.Y0)

theorem physicalTailConstant_nonneg (P : PacketData ι) (a b J0 : ℕ) :
    0 ≤ physicalTailConstant P a b J0 := by
  unfold physicalTailConstant
  have hW := actualW_nonneg P.rho P.sigma J0
  have hM := commonMaskCoefficientMass_nonneg P a b
  have hY := P.Y0_pos
  positivity

/-- Genuine pointwise t^-2 decay of the entire masked physical q integral.
No target-tail estimate or per-mode replacement is an input. -/
theorem maskedPhysicalHeight_norm_le_quadratic (P : PacketData ι)
    (a b J0 : ℕ) {t : ℝ} (ht : t ≠ 0) :
    ‖maskedPhysicalHeight P a b t‖ ≤ physicalTailConstant P a b J0/t^2 := by
  have h := k_common_norm_fullIntegral_le_quadratic
    (restrictM P a b) ht J0
  calc
    ‖maskedPhysicalHeight P a b t‖ ≤
        actualW (restrictM P a b).rho (restrictM P a b).sigma J0 *
          coefficientMass (restrictM P a b) *
          (2560 / ((restrictM P a b).Y0^2 * t^2)) *
          ((255/16 : ℝ) * (restrictM P a b).Y0) := by
      simpa only [maskedPhysicalHeight] using h
    _ = physicalTailConstant P a b J0/t^2 := by
      unfold physicalTailConstant
      rw [commonMaskCoefficientMass_eq_actual]
      dsimp only [restrictM]
      field_simp [P.Y0_pos.ne', ht]
      ring

/-- The full physical packet energy on positive high heights has explicit
T^-3 decay, not merely Fourier-mode truncation convergence. -/
theorem maskedPhysicalHeight_positive_tail (P : PacketData ι)
    (a b J0 : ℕ) {T : ℝ} (hT : 0 < T) :
    IntegrableOn (fun t : ℝ => ‖maskedPhysicalHeight P a b t‖^2) (Ioi T) ∧
      0 ≤ (∫ t in Ioi T, ‖maskedPhysicalHeight P a b t‖^2) ∧
      (∫ t in Ioi T, ‖maskedPhysicalHeight P a b t‖^2) ≤
        (physicalTailConstant P a b J0)^2/(3*T^3) := by
  apply quadratic_energy_tail (maskedPhysicalHeight_continuous P a b)
    (physicalTailConstant_nonneg P a b J0) hT
  intro t ht
  have htp : 0 < t := hT.trans ht
  exact maskedPhysicalHeight_norm_le_quadratic P a b J0 htp.ne'

/-- Imaginary-order K is even in the common height; all finite physical
packet weights remain fixed while the kernel changes sign in t. -/
theorem maskedPhysicalHeight_neg (P : PacketData ι) (a b : ℕ) (t : ℝ) :
    maskedPhysicalHeight P a b (-t) = maskedPhysicalHeight P a b t := by
  unfold maskedPhysicalHeight
  apply integral_congr_ae
  exact Eventually.of_forall (fun q => by
    simp only [kPhysical, commonHeight, imaginaryOrderK_neg])

/-- Closed two-sided height tail. The two endpoints have zero Lebesgue
measure; the positive-side integral can use the convenient open ray. -/
def physicalHeightTail (T : ℝ) : Set ℝ := {t | T ≤ |t|}

theorem physicalHeightTail_eq_union (T : ℝ) :
    physicalHeightTail T = Iic (-T) ∪ Ici T := by
  ext t
  simp only [physicalHeightTail, mem_setOf_eq, mem_union, mem_Iic, mem_Ici]
  constructor
  · intro ht
    by_cases hneg : t < 0
    · left
      rw [abs_of_neg hneg] at ht
      linarith
    · right
      rwa [abs_of_nonneg (le_of_not_gt hneg)] at ht
  · intro ht
    rcases ht with hneg | hpos
    · have h : -t ≤ |t| := neg_le_abs t
      linarith
    · exact hpos.trans (le_abs_self t)

/-- Actual same-mask full physical height energy outside |t|<T. The
coefficient is explicit, and both tails together cost only 2/3 T^-3. -/
theorem maskedPhysicalHeight_two_sided_tail (P : PacketData ι)
    (a b J0 : ℕ) {T : ℝ} (hT : 0 < T) :
    (∫ t in physicalHeightTail T, ‖maskedPhysicalHeight P a b t‖^2) ≤
      2 * (physicalTailConstant P a b J0)^2/(3*T^3) := by
  let f : ℝ → ℝ := fun t => ‖maskedPhysicalHeight P a b t‖^2
  have hfi : Integrable f := maskedPhysicalHeight_norm_sq_integrable P a b
  have hdis : Disjoint (Iic (-T)) (Ici T) := by
    apply Set.disjoint_left.mpr
    intro t htneg htpos
    exact (not_le_of_gt (by linarith : -T < T)) (htpos.trans htneg)
  have htail := (maskedPhysicalHeight_positive_tail P a b J0 hT).2.2
  calc
    (∫ t in physicalHeightTail T, ‖maskedPhysicalHeight P a b t‖^2) =
        (∫ t in Iic (-T), f t) + (∫ t in Ioi T, f t) := by
      rw [physicalHeightTail_eq_union,
        setIntegral_union hdis measurableSet_Ici hfi.integrableOn hfi.integrableOn,
        integral_Ici_eq_integral_Ioi]
    _ = 2 * (∫ t in Ioi T, f t) := by
      rw [negative_energy_tail_eq_positive
        (maskedPhysicalHeight_neg P a b) T]
      ring
    _ ≤ 2 * (physicalTailConstant P a b J0)^2/(3*T^3) := by
      calc
        2 * (∫ t in Ioi T, f t) ≤
            2 * ((physicalTailConstant P a b J0)^2/(3*T^3)) :=
          mul_le_mul_of_nonneg_left htail (by norm_num)
        _ = _ := by ring

end
end ImbalancedChen.Part3.ActualCommonMaskPhysicalHeightTailSourceOnly
