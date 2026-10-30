import ImbalancedChen.Certificates.PairedV2Batch4To64Data
import ImbalancedChen.Certificates.PairedV2Geometry
import ImbalancedChen.Certificates.PairedV2Batch4To64Rows0004To0012
import ImbalancedChen.Certificates.PairedV2Batch4To64Rows0012To0020
import ImbalancedChen.Certificates.PairedV2Batch4To64Rows0020To0028
import ImbalancedChen.Certificates.PairedV2Batch4To64Rows0028To0036
import ImbalancedChen.Certificates.PairedV2Batch4To64Rows0036To0044
import ImbalancedChen.Certificates.PairedV2Batch4To64Rows0044To0052
import ImbalancedChen.Certificates.PairedV2Batch4To64Rows0052To0060
import ImbalancedChen.Certificates.PairedV2Batch4To64Rows0060To0064
import ImbalancedChen.Certificates.PairedV2Batch4To64GeometryChecked
import ImbalancedChen.Certificates.PairedV2Batch4To64CertificateInputs
import ImbalancedChen.Certificates.PairedV2Batch4To64LowerSum
import ImbalancedChen.Certificates.PairedV2Batch4To64UpperSum

/-!
Actual adopted E0 cells at original ordinals [4,64). Each check has its own
proof term, then the accepted checker bounds the sum of real integrals.
Local Fin indices are offsets; all source ordinals and certificate names remain global.
The finite sum is not asserted equal to the full mask or to a union integral.
-/

namespace ImbalancedChen.Certificates.PairedV2.Batch4To64

open MeasureTheory Set
open scoped BigOperators Interval

set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

theorem rowOrdinal_range (i : Fin 60) :
    4 ≤ rowOrdinal i ∧ rowOrdinal i < 64 := by
  dsimp only [rowOrdinal]
  omega

theorem row_group (i : Fin 60) : rowGroup i = "E0" := rfl
theorem discarded_floor_zero (i : Fin 60) : rowDiscardedFloorQ80 i = 0 := rfl

theorem certificates_checked (i : Fin 60) : (certificates i).check = true := by
  fin_cases i
  · exact row0004_checked
  · exact row0005_checked
  · exact row0006_checked
  · exact row0007_checked
  · exact row0008_checked
  · exact row0009_checked
  · exact row0010_checked
  · exact row0011_checked
  · exact row0012_checked
  · exact row0013_checked
  · exact row0014_checked
  · exact row0015_checked
  · exact row0016_checked
  · exact row0017_checked
  · exact row0018_checked
  · exact row0019_checked
  · exact row0020_checked
  · exact row0021_checked
  · exact row0022_checked
  · exact row0023_checked
  · exact row0024_checked
  · exact row0025_checked
  · exact row0026_checked
  · exact row0027_checked
  · exact row0028_checked
  · exact row0029_checked
  · exact row0030_checked
  · exact row0031_checked
  · exact row0032_checked
  · exact row0033_checked
  · exact row0034_checked
  · exact row0035_checked
  · exact row0036_checked
  · exact row0037_checked
  · exact row0038_checked
  · exact row0039_checked
  · exact row0040_checked
  · exact row0041_checked
  · exact row0042_checked
  · exact row0043_checked
  · exact row0044_checked
  · exact row0045_checked
  · exact row0046_checked
  · exact row0047_checked
  · exact row0048_checked
  · exact row0049_checked
  · exact row0050_checked
  · exact row0051_checked
  · exact row0052_checked
  · exact row0053_checked
  · exact row0054_checked
  · exact row0055_checked
  · exact row0056_checked
  · exact row0057_checked
  · exact row0058_checked
  · exact row0059_checked
  · exact row0060_checked
  · exact row0061_checked
  · exact row0062_checked
  · exact row0063_checked

theorem fibre_argument (i : Fin 60) {t u z w : ℝ}
    (hs : openFibreSupport (rowIndices i).1 (rowIndices i).2 (rowZ i) t u z w) :
    (a : ℝ) < w ∧ w < z ∧ z < u ∧ u < (h : ℝ) ∧
      (h : ℝ) < t ∧ t < (d : ℝ) ∧
      (7 / 3 : ℝ) ≤ (1 - t - u - z - w) / z :=
  (geometry_checked i).fibre_argument hs

theorem fibre_nonempty (i : Fin 60) :
    ∃ t u z w : ℝ, openFibreSupport (rowIndices i).1 (rowIndices i).2 (rowZ i) t u z w :=
  (geometry_checked i).fibre_nonempty

noncomputable def rowIntegral (i : Fin 60) : ℝ :=
  pairedLocalIntegral (K : ℝ) a (tLower (rowIndices i).1)
    (tUpper (rowIndices i).1) (uLower (rowIndices i).2)
    (uUpper (rowIndices i).2) (rowZ i)

noncomputable def integral : ℝ := ∑ i : Fin 60, rowIntegral i

theorem rowIntegral_eq_certificate (i : Fin 60) :
    rowIntegral i = pairedLocalIntegral ((certificates i).K : ℝ)
      (certificates i).a (certificates i).tl (certificates i).tr
      (certificates i).ul (certificates i).ur (certificates i).Z := by
  rcases certificate_inputs i with ⟨hK, ha, htl, htr, hul, hur, hZ⟩
  rw [hK, ha, htl, htr, hul, hur, hZ]
  rfl

theorem rowIntegral_bounds (i : Fin 60) :
    ((certificates i).lower : ℝ) ≤ rowIntegral i ∧
      rowIntegral i ≤ ((certificates i).upper : ℝ) := by
  rw [rowIntegral_eq_certificate]
  exact (certificates i).check_sound (certificates_checked i)

/-- The finite sum exposes the actual fourfold manuscript kernel. -/
theorem integral_semantics :
    integral = ((K : ℝ) / 80) * ∑ i : Fin 60,
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

end ImbalancedChen.Certificates.PairedV2.Batch4To64
