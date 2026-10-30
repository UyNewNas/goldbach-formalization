import ImbalancedChen.Certificates.PairedV2Batch64To128Data
import ImbalancedChen.Certificates.PairedV2Geometry
import ImbalancedChen.Certificates.PairedV2Batch64To128Rows0064To0072
import ImbalancedChen.Certificates.PairedV2Batch64To128Rows0072To0080
import ImbalancedChen.Certificates.PairedV2Batch64To128Rows0080To0088
import ImbalancedChen.Certificates.PairedV2Batch64To128Rows0088To0096
import ImbalancedChen.Certificates.PairedV2Batch64To128Rows0096To0104
import ImbalancedChen.Certificates.PairedV2Batch64To128Rows0104To0112
import ImbalancedChen.Certificates.PairedV2Batch64To128Rows0112To0120
import ImbalancedChen.Certificates.PairedV2Batch64To128Rows0120To0128
import ImbalancedChen.Certificates.PairedV2Batch64To128GeometryChecked
import ImbalancedChen.Certificates.PairedV2Batch64To128CertificateInputs
import ImbalancedChen.Certificates.PairedV2Batch64To128LowerSum
import ImbalancedChen.Certificates.PairedV2Batch64To128UpperSum

/-!
Actual adopted E0 cells at original ordinals [64,128). Each check has its own
proof term, then the accepted checker bounds the sum of real integrals.
Local Fin indices are offsets; all source ordinals and certificate names remain global.
The finite sum is not asserted equal to the full mask or to a union integral.
-/

namespace ImbalancedChen.Certificates.PairedV2.Batch64To128

open MeasureTheory Set
open scoped BigOperators Interval

set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

theorem rowOrdinal_range (i : Fin 64) :
    64 ≤ rowOrdinal i ∧ rowOrdinal i < 128 := by
  dsimp only [rowOrdinal]
  omega

theorem row_group (i : Fin 64) : rowGroup i = "E0" := rfl
theorem discarded_floor_zero (i : Fin 64) : rowDiscardedFloorQ80 i = 0 := rfl

theorem certificates_checked (i : Fin 64) : (certificates i).check = true := by
  fin_cases i
  · exact row0064_checked
  · exact row0065_checked
  · exact row0066_checked
  · exact row0067_checked
  · exact row0068_checked
  · exact row0069_checked
  · exact row0070_checked
  · exact row0071_checked
  · exact row0072_checked
  · exact row0073_checked
  · exact row0074_checked
  · exact row0075_checked
  · exact row0076_checked
  · exact row0077_checked
  · exact row0078_checked
  · exact row0079_checked
  · exact row0080_checked
  · exact row0081_checked
  · exact row0082_checked
  · exact row0083_checked
  · exact row0084_checked
  · exact row0085_checked
  · exact row0086_checked
  · exact row0087_checked
  · exact row0088_checked
  · exact row0089_checked
  · exact row0090_checked
  · exact row0091_checked
  · exact row0092_checked
  · exact row0093_checked
  · exact row0094_checked
  · exact row0095_checked
  · exact row0096_checked
  · exact row0097_checked
  · exact row0098_checked
  · exact row0099_checked
  · exact row0100_checked
  · exact row0101_checked
  · exact row0102_checked
  · exact row0103_checked
  · exact row0104_checked
  · exact row0105_checked
  · exact row0106_checked
  · exact row0107_checked
  · exact row0108_checked
  · exact row0109_checked
  · exact row0110_checked
  · exact row0111_checked
  · exact row0112_checked
  · exact row0113_checked
  · exact row0114_checked
  · exact row0115_checked
  · exact row0116_checked
  · exact row0117_checked
  · exact row0118_checked
  · exact row0119_checked
  · exact row0120_checked
  · exact row0121_checked
  · exact row0122_checked
  · exact row0123_checked
  · exact row0124_checked
  · exact row0125_checked
  · exact row0126_checked
  · exact row0127_checked

theorem fibre_argument (i : Fin 64) {t u z w : ℝ}
    (hs : openFibreSupport (rowIndices i).1 (rowIndices i).2 (rowZ i) t u z w) :
    (a : ℝ) < w ∧ w < z ∧ z < u ∧ u < (h : ℝ) ∧
      (h : ℝ) < t ∧ t < (d : ℝ) ∧
      (7 / 3 : ℝ) ≤ (1 - t - u - z - w) / z :=
  (geometry_checked i).fibre_argument hs

theorem fibre_nonempty (i : Fin 64) :
    ∃ t u z w : ℝ, openFibreSupport (rowIndices i).1 (rowIndices i).2 (rowZ i) t u z w :=
  (geometry_checked i).fibre_nonempty

noncomputable def rowIntegral (i : Fin 64) : ℝ :=
  pairedLocalIntegral (K : ℝ) a (tLower (rowIndices i).1)
    (tUpper (rowIndices i).1) (uLower (rowIndices i).2)
    (uUpper (rowIndices i).2) (rowZ i)

noncomputable def integral : ℝ := ∑ i : Fin 64, rowIntegral i

theorem rowIntegral_eq_certificate (i : Fin 64) :
    rowIntegral i = pairedLocalIntegral ((certificates i).K : ℝ)
      (certificates i).a (certificates i).tl (certificates i).tr
      (certificates i).ul (certificates i).ur (certificates i).Z := by
  rcases certificate_inputs i with ⟨hK, ha, htl, htr, hul, hur, hZ⟩
  rw [hK, ha, htl, htr, hul, hur, hZ]
  rfl

theorem rowIntegral_bounds (i : Fin 64) :
    ((certificates i).lower : ℝ) ≤ rowIntegral i ∧
      rowIntegral i ≤ ((certificates i).upper : ℝ) := by
  rw [rowIntegral_eq_certificate]
  exact (certificates i).check_sound (certificates_checked i)

/-- The finite sum exposes the actual fourfold manuscript kernel. -/
theorem integral_semantics :
    integral = ((K : ℝ) / 80) * ∑ i : Fin 64,
      ∫ t in (tLower (rowIndices i).1 : ℝ)..(tUpper (rowIndices i).1 : ℝ),
      ∫ u in (uLower (rowIndices i).2 : ℝ)..(uUpper (rowIndices i).2 : ℝ),
      ∫ z in (a : ℝ)..(rowZ i : ℝ), ∫ w in (a : ℝ)..z,
        1 / (t * u * z ^ 2 * w) := by
  simp only [integral, rowIntegral, pairedLocalIntegral, pairedFibreKernel_eq, Finset.mul_sum]

/-- Concrete acceptance, checker soundness, and actual-object equality. -/
theorem integral_bounds : (lowerBound : ℝ) ≤ integral ∧ integral ≤ (upperBound : ℝ) := by
  have hs := PairedIntegralCertificate.sum_check_sound Finset.univ certificates
    (fun i _ => certificates_checked i)
  rw [lower_sum, upper_sum] at hs
  simpa only [integral, ← rowIntegral_eq_certificate] using hs

theorem integral_pos : 0 < integral := by
  exact lt_of_lt_of_le (by norm_num [lowerBound]) integral_bounds.1

end ImbalancedChen.Certificates.PairedV2.Batch64To128
