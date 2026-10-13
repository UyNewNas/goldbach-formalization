import ImbalancedChen.Certificates.PairedV2Batch128To192Data
import ImbalancedChen.Certificates.PairedV2Geometry

/-!
Actual adopted E0 cells at original ordinals [128,192). Each check has its own
proof term, then the accepted checker bounds the sum of real integrals.
Local Fin indices are offsets; all source ordinals and certificate names remain global.
The finite sum is not asserted equal to the full mask or to a union integral.
-/

namespace ImbalancedChen.Certificates.PairedV2.Batch128To192

open MeasureTheory Set
open scoped BigOperators Interval

set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

theorem rowOrdinal_range (i : Fin 64) :
    128 ≤ rowOrdinal i ∧ rowOrdinal i < 192 := by
  dsimp only [rowOrdinal]
  omega

theorem row_group (i : Fin 64) : rowGroup i = "E0" := rfl
theorem discarded_floor_zero (i : Fin 64) : rowDiscardedFloorQ80 i = 0 := rfl

theorem row0128_checked : certificate0128.check = true := by
  norm_num [certificate0128, PairedIntegralCertificate.check, PairedIntegralCertificate.Valid, RationalLogCertificate.check, RationalLogCertificate.Valid, PairedIntegralCertificate.productLower, PairedIntegralCertificate.productUpper, PairedIntegralCertificate.bracketLower, PairedIntegralCertificate.bracketUpper, logSeriesLower, logSeriesUpper, logParameter, Finset.sum_range_succ, tLower, tUpper, uLower, uUpper, a, h, d, mu, K]

theorem row0129_checked : certificate0129.check = true := by
  norm_num [certificate0129, PairedIntegralCertificate.check, PairedIntegralCertificate.Valid, RationalLogCertificate.check, RationalLogCertificate.Valid, PairedIntegralCertificate.productLower, PairedIntegralCertificate.productUpper, PairedIntegralCertificate.bracketLower, PairedIntegralCertificate.bracketUpper, logSeriesLower, logSeriesUpper, logParameter, Finset.sum_range_succ, tLower, tUpper, uLower, uUpper, a, h, d, mu, K]

theorem row0130_checked : certificate0130.check = true := by
  norm_num [certificate0130, PairedIntegralCertificate.check, PairedIntegralCertificate.Valid, RationalLogCertificate.check, RationalLogCertificate.Valid, PairedIntegralCertificate.productLower, PairedIntegralCertificate.productUpper, PairedIntegralCertificate.bracketLower, PairedIntegralCertificate.bracketUpper, logSeriesLower, logSeriesUpper, logParameter, Finset.sum_range_succ, tLower, tUpper, uLower, uUpper, a, h, d, mu, K]

theorem row0131_checked : certificate0131.check = true := by
  norm_num [certificate0131, PairedIntegralCertificate.check, PairedIntegralCertificate.Valid, RationalLogCertificate.check, RationalLogCertificate.Valid, PairedIntegralCertificate.productLower, PairedIntegralCertificate.productUpper, PairedIntegralCertificate.bracketLower, PairedIntegralCertificate.bracketUpper, logSeriesLower, logSeriesUpper, logParameter, Finset.sum_range_succ, tLower, tUpper, uLower, uUpper, a, h, d, mu, K]

theorem row0132_checked : certificate0132.check = true := by
  norm_num [certificate0132, PairedIntegralCertificate.check, PairedIntegralCertificate.Valid, RationalLogCertificate.check, RationalLogCertificate.Valid, PairedIntegralCertificate.productLower, PairedIntegralCertificate.productUpper, PairedIntegralCertificate.bracketLower, PairedIntegralCertificate.bracketUpper, logSeriesLower, logSeriesUpper, logParameter, Finset.sum_range_succ, tLower, tUpper, uLower, uUpper, a, h, d, mu, K]

theorem row0133_checked : certificate0133.check = true := by
  norm_num [certificate0133, PairedIntegralCertificate.check, PairedIntegralCertificate.Valid, RationalLogCertificate.check, RationalLogCertificate.Valid, PairedIntegralCertificate.productLower, PairedIntegralCertificate.productUpper, PairedIntegralCertificate.bracketLower, PairedIntegralCertificate.bracketUpper, logSeriesLower, logSeriesUpper, logParameter, Finset.sum_range_succ, tLower, tUpper, uLower, uUpper, a, h, d, mu, K]

theorem row0134_checked : certificate0134.check = true := by
  norm_num [certificate0134, PairedIntegralCertificate.check, PairedIntegralCertificate.Valid, RationalLogCertificate.check, RationalLogCertificate.Valid, PairedIntegralCertificate.productLower, PairedIntegralCertificate.productUpper, PairedIntegralCertificate.bracketLower, PairedIntegralCertificate.bracketUpper, logSeriesLower, logSeriesUpper, logParameter, Finset.sum_range_succ, tLower, tUpper, uLower, uUpper, a, h, d, mu, K]

theorem row0135_checked : certificate0135.check = true := by
  norm_num [certificate0135, PairedIntegralCertificate.check, PairedIntegralCertificate.Valid, RationalLogCertificate.check, RationalLogCertificate.Valid, PairedIntegralCertificate.productLower, PairedIntegralCertificate.productUpper, PairedIntegralCertificate.bracketLower, PairedIntegralCertificate.bracketUpper, logSeriesLower, logSeriesUpper, logParameter, Finset.sum_range_succ, tLower, tUpper, uLower, uUpper, a, h, d, mu, K]

theorem row0136_checked : certificate0136.check = true := by
  norm_num [certificate0136, PairedIntegralCertificate.check, PairedIntegralCertificate.Valid, RationalLogCertificate.check, RationalLogCertificate.Valid, PairedIntegralCertificate.productLower, PairedIntegralCertificate.productUpper, PairedIntegralCertificate.bracketLower, PairedIntegralCertificate.bracketUpper, logSeriesLower, logSeriesUpper, logParameter, Finset.sum_range_succ, tLower, tUpper, uLower, uUpper, a, h, d, mu, K]

theorem row0137_checked : certificate0137.check = true := by
  norm_num [certificate0137, PairedIntegralCertificate.check, PairedIntegralCertificate.Valid, RationalLogCertificate.check, RationalLogCertificate.Valid, PairedIntegralCertificate.productLower, PairedIntegralCertificate.productUpper, PairedIntegralCertificate.bracketLower, PairedIntegralCertificate.bracketUpper, logSeriesLower, logSeriesUpper, logParameter, Finset.sum_range_succ, tLower, tUpper, uLower, uUpper, a, h, d, mu, K]

theorem row0138_checked : certificate0138.check = true := by
  norm_num [certificate0138, PairedIntegralCertificate.check, PairedIntegralCertificate.Valid, RationalLogCertificate.check, RationalLogCertificate.Valid, PairedIntegralCertificate.productLower, PairedIntegralCertificate.productUpper, PairedIntegralCertificate.bracketLower, PairedIntegralCertificate.bracketUpper, logSeriesLower, logSeriesUpper, logParameter, Finset.sum_range_succ, tLower, tUpper, uLower, uUpper, a, h, d, mu, K]

theorem row0139_checked : certificate0139.check = true := by
  norm_num [certificate0139, PairedIntegralCertificate.check, PairedIntegralCertificate.Valid, RationalLogCertificate.check, RationalLogCertificate.Valid, PairedIntegralCertificate.productLower, PairedIntegralCertificate.productUpper, PairedIntegralCertificate.bracketLower, PairedIntegralCertificate.bracketUpper, logSeriesLower, logSeriesUpper, logParameter, Finset.sum_range_succ, tLower, tUpper, uLower, uUpper, a, h, d, mu, K]

theorem row0140_checked : certificate0140.check = true := by
  norm_num [certificate0140, PairedIntegralCertificate.check, PairedIntegralCertificate.Valid, RationalLogCertificate.check, RationalLogCertificate.Valid, PairedIntegralCertificate.productLower, PairedIntegralCertificate.productUpper, PairedIntegralCertificate.bracketLower, PairedIntegralCertificate.bracketUpper, logSeriesLower, logSeriesUpper, logParameter, Finset.sum_range_succ, tLower, tUpper, uLower, uUpper, a, h, d, mu, K]

theorem row0141_checked : certificate0141.check = true := by
  norm_num [certificate0141, PairedIntegralCertificate.check, PairedIntegralCertificate.Valid, RationalLogCertificate.check, RationalLogCertificate.Valid, PairedIntegralCertificate.productLower, PairedIntegralCertificate.productUpper, PairedIntegralCertificate.bracketLower, PairedIntegralCertificate.bracketUpper, logSeriesLower, logSeriesUpper, logParameter, Finset.sum_range_succ, tLower, tUpper, uLower, uUpper, a, h, d, mu, K]

theorem row0142_checked : certificate0142.check = true := by
  norm_num [certificate0142, PairedIntegralCertificate.check, PairedIntegralCertificate.Valid, RationalLogCertificate.check, RationalLogCertificate.Valid, PairedIntegralCertificate.productLower, PairedIntegralCertificate.productUpper, PairedIntegralCertificate.bracketLower, PairedIntegralCertificate.bracketUpper, logSeriesLower, logSeriesUpper, logParameter, Finset.sum_range_succ, tLower, tUpper, uLower, uUpper, a, h, d, mu, K]

theorem row0143_checked : certificate0143.check = true := by
  norm_num [certificate0143, PairedIntegralCertificate.check, PairedIntegralCertificate.Valid, RationalLogCertificate.check, RationalLogCertificate.Valid, PairedIntegralCertificate.productLower, PairedIntegralCertificate.productUpper, PairedIntegralCertificate.bracketLower, PairedIntegralCertificate.bracketUpper, logSeriesLower, logSeriesUpper, logParameter, Finset.sum_range_succ, tLower, tUpper, uLower, uUpper, a, h, d, mu, K]

theorem row0144_checked : certificate0144.check = true := by
  norm_num [certificate0144, PairedIntegralCertificate.check, PairedIntegralCertificate.Valid, RationalLogCertificate.check, RationalLogCertificate.Valid, PairedIntegralCertificate.productLower, PairedIntegralCertificate.productUpper, PairedIntegralCertificate.bracketLower, PairedIntegralCertificate.bracketUpper, logSeriesLower, logSeriesUpper, logParameter, Finset.sum_range_succ, tLower, tUpper, uLower, uUpper, a, h, d, mu, K]

theorem row0145_checked : certificate0145.check = true := by
  norm_num [certificate0145, PairedIntegralCertificate.check, PairedIntegralCertificate.Valid, RationalLogCertificate.check, RationalLogCertificate.Valid, PairedIntegralCertificate.productLower, PairedIntegralCertificate.productUpper, PairedIntegralCertificate.bracketLower, PairedIntegralCertificate.bracketUpper, logSeriesLower, logSeriesUpper, logParameter, Finset.sum_range_succ, tLower, tUpper, uLower, uUpper, a, h, d, mu, K]

theorem row0146_checked : certificate0146.check = true := by
  norm_num [certificate0146, PairedIntegralCertificate.check, PairedIntegralCertificate.Valid, RationalLogCertificate.check, RationalLogCertificate.Valid, PairedIntegralCertificate.productLower, PairedIntegralCertificate.productUpper, PairedIntegralCertificate.bracketLower, PairedIntegralCertificate.bracketUpper, logSeriesLower, logSeriesUpper, logParameter, Finset.sum_range_succ, tLower, tUpper, uLower, uUpper, a, h, d, mu, K]

theorem row0147_checked : certificate0147.check = true := by
  norm_num [certificate0147, PairedIntegralCertificate.check, PairedIntegralCertificate.Valid, RationalLogCertificate.check, RationalLogCertificate.Valid, PairedIntegralCertificate.productLower, PairedIntegralCertificate.productUpper, PairedIntegralCertificate.bracketLower, PairedIntegralCertificate.bracketUpper, logSeriesLower, logSeriesUpper, logParameter, Finset.sum_range_succ, tLower, tUpper, uLower, uUpper, a, h, d, mu, K]

theorem row0148_checked : certificate0148.check = true := by
  norm_num [certificate0148, PairedIntegralCertificate.check, PairedIntegralCertificate.Valid, RationalLogCertificate.check, RationalLogCertificate.Valid, PairedIntegralCertificate.productLower, PairedIntegralCertificate.productUpper, PairedIntegralCertificate.bracketLower, PairedIntegralCertificate.bracketUpper, logSeriesLower, logSeriesUpper, logParameter, Finset.sum_range_succ, tLower, tUpper, uLower, uUpper, a, h, d, mu, K]

theorem row0149_checked : certificate0149.check = true := by
  norm_num [certificate0149, PairedIntegralCertificate.check, PairedIntegralCertificate.Valid, RationalLogCertificate.check, RationalLogCertificate.Valid, PairedIntegralCertificate.productLower, PairedIntegralCertificate.productUpper, PairedIntegralCertificate.bracketLower, PairedIntegralCertificate.bracketUpper, logSeriesLower, logSeriesUpper, logParameter, Finset.sum_range_succ, tLower, tUpper, uLower, uUpper, a, h, d, mu, K]

theorem row0150_checked : certificate0150.check = true := by
  norm_num [certificate0150, PairedIntegralCertificate.check, PairedIntegralCertificate.Valid, RationalLogCertificate.check, RationalLogCertificate.Valid, PairedIntegralCertificate.productLower, PairedIntegralCertificate.productUpper, PairedIntegralCertificate.bracketLower, PairedIntegralCertificate.bracketUpper, logSeriesLower, logSeriesUpper, logParameter, Finset.sum_range_succ, tLower, tUpper, uLower, uUpper, a, h, d, mu, K]

theorem row0151_checked : certificate0151.check = true := by
  norm_num [certificate0151, PairedIntegralCertificate.check, PairedIntegralCertificate.Valid, RationalLogCertificate.check, RationalLogCertificate.Valid, PairedIntegralCertificate.productLower, PairedIntegralCertificate.productUpper, PairedIntegralCertificate.bracketLower, PairedIntegralCertificate.bracketUpper, logSeriesLower, logSeriesUpper, logParameter, Finset.sum_range_succ, tLower, tUpper, uLower, uUpper, a, h, d, mu, K]

theorem row0152_checked : certificate0152.check = true := by
  norm_num [certificate0152, PairedIntegralCertificate.check, PairedIntegralCertificate.Valid, RationalLogCertificate.check, RationalLogCertificate.Valid, PairedIntegralCertificate.productLower, PairedIntegralCertificate.productUpper, PairedIntegralCertificate.bracketLower, PairedIntegralCertificate.bracketUpper, logSeriesLower, logSeriesUpper, logParameter, Finset.sum_range_succ, tLower, tUpper, uLower, uUpper, a, h, d, mu, K]

theorem row0153_checked : certificate0153.check = true := by
  norm_num [certificate0153, PairedIntegralCertificate.check, PairedIntegralCertificate.Valid, RationalLogCertificate.check, RationalLogCertificate.Valid, PairedIntegralCertificate.productLower, PairedIntegralCertificate.productUpper, PairedIntegralCertificate.bracketLower, PairedIntegralCertificate.bracketUpper, logSeriesLower, logSeriesUpper, logParameter, Finset.sum_range_succ, tLower, tUpper, uLower, uUpper, a, h, d, mu, K]

theorem row0154_checked : certificate0154.check = true := by
  norm_num [certificate0154, PairedIntegralCertificate.check, PairedIntegralCertificate.Valid, RationalLogCertificate.check, RationalLogCertificate.Valid, PairedIntegralCertificate.productLower, PairedIntegralCertificate.productUpper, PairedIntegralCertificate.bracketLower, PairedIntegralCertificate.bracketUpper, logSeriesLower, logSeriesUpper, logParameter, Finset.sum_range_succ, tLower, tUpper, uLower, uUpper, a, h, d, mu, K]

theorem row0155_checked : certificate0155.check = true := by
  norm_num [certificate0155, PairedIntegralCertificate.check, PairedIntegralCertificate.Valid, RationalLogCertificate.check, RationalLogCertificate.Valid, PairedIntegralCertificate.productLower, PairedIntegralCertificate.productUpper, PairedIntegralCertificate.bracketLower, PairedIntegralCertificate.bracketUpper, logSeriesLower, logSeriesUpper, logParameter, Finset.sum_range_succ, tLower, tUpper, uLower, uUpper, a, h, d, mu, K]

theorem row0156_checked : certificate0156.check = true := by
  norm_num [certificate0156, PairedIntegralCertificate.check, PairedIntegralCertificate.Valid, RationalLogCertificate.check, RationalLogCertificate.Valid, PairedIntegralCertificate.productLower, PairedIntegralCertificate.productUpper, PairedIntegralCertificate.bracketLower, PairedIntegralCertificate.bracketUpper, logSeriesLower, logSeriesUpper, logParameter, Finset.sum_range_succ, tLower, tUpper, uLower, uUpper, a, h, d, mu, K]

theorem row0157_checked : certificate0157.check = true := by
  norm_num [certificate0157, PairedIntegralCertificate.check, PairedIntegralCertificate.Valid, RationalLogCertificate.check, RationalLogCertificate.Valid, PairedIntegralCertificate.productLower, PairedIntegralCertificate.productUpper, PairedIntegralCertificate.bracketLower, PairedIntegralCertificate.bracketUpper, logSeriesLower, logSeriesUpper, logParameter, Finset.sum_range_succ, tLower, tUpper, uLower, uUpper, a, h, d, mu, K]

theorem row0158_checked : certificate0158.check = true := by
  norm_num [certificate0158, PairedIntegralCertificate.check, PairedIntegralCertificate.Valid, RationalLogCertificate.check, RationalLogCertificate.Valid, PairedIntegralCertificate.productLower, PairedIntegralCertificate.productUpper, PairedIntegralCertificate.bracketLower, PairedIntegralCertificate.bracketUpper, logSeriesLower, logSeriesUpper, logParameter, Finset.sum_range_succ, tLower, tUpper, uLower, uUpper, a, h, d, mu, K]

theorem row0159_checked : certificate0159.check = true := by
  norm_num [certificate0159, PairedIntegralCertificate.check, PairedIntegralCertificate.Valid, RationalLogCertificate.check, RationalLogCertificate.Valid, PairedIntegralCertificate.productLower, PairedIntegralCertificate.productUpper, PairedIntegralCertificate.bracketLower, PairedIntegralCertificate.bracketUpper, logSeriesLower, logSeriesUpper, logParameter, Finset.sum_range_succ, tLower, tUpper, uLower, uUpper, a, h, d, mu, K]

theorem row0160_checked : certificate0160.check = true := by
  norm_num [certificate0160, PairedIntegralCertificate.check, PairedIntegralCertificate.Valid, RationalLogCertificate.check, RationalLogCertificate.Valid, PairedIntegralCertificate.productLower, PairedIntegralCertificate.productUpper, PairedIntegralCertificate.bracketLower, PairedIntegralCertificate.bracketUpper, logSeriesLower, logSeriesUpper, logParameter, Finset.sum_range_succ, tLower, tUpper, uLower, uUpper, a, h, d, mu, K]

theorem row0161_checked : certificate0161.check = true := by
  norm_num [certificate0161, PairedIntegralCertificate.check, PairedIntegralCertificate.Valid, RationalLogCertificate.check, RationalLogCertificate.Valid, PairedIntegralCertificate.productLower, PairedIntegralCertificate.productUpper, PairedIntegralCertificate.bracketLower, PairedIntegralCertificate.bracketUpper, logSeriesLower, logSeriesUpper, logParameter, Finset.sum_range_succ, tLower, tUpper, uLower, uUpper, a, h, d, mu, K]

theorem row0162_checked : certificate0162.check = true := by
  norm_num [certificate0162, PairedIntegralCertificate.check, PairedIntegralCertificate.Valid, RationalLogCertificate.check, RationalLogCertificate.Valid, PairedIntegralCertificate.productLower, PairedIntegralCertificate.productUpper, PairedIntegralCertificate.bracketLower, PairedIntegralCertificate.bracketUpper, logSeriesLower, logSeriesUpper, logParameter, Finset.sum_range_succ, tLower, tUpper, uLower, uUpper, a, h, d, mu, K]

theorem row0163_checked : certificate0163.check = true := by
  norm_num [certificate0163, PairedIntegralCertificate.check, PairedIntegralCertificate.Valid, RationalLogCertificate.check, RationalLogCertificate.Valid, PairedIntegralCertificate.productLower, PairedIntegralCertificate.productUpper, PairedIntegralCertificate.bracketLower, PairedIntegralCertificate.bracketUpper, logSeriesLower, logSeriesUpper, logParameter, Finset.sum_range_succ, tLower, tUpper, uLower, uUpper, a, h, d, mu, K]

theorem row0164_checked : certificate0164.check = true := by
  norm_num [certificate0164, PairedIntegralCertificate.check, PairedIntegralCertificate.Valid, RationalLogCertificate.check, RationalLogCertificate.Valid, PairedIntegralCertificate.productLower, PairedIntegralCertificate.productUpper, PairedIntegralCertificate.bracketLower, PairedIntegralCertificate.bracketUpper, logSeriesLower, logSeriesUpper, logParameter, Finset.sum_range_succ, tLower, tUpper, uLower, uUpper, a, h, d, mu, K]

theorem row0165_checked : certificate0165.check = true := by
  norm_num [certificate0165, PairedIntegralCertificate.check, PairedIntegralCertificate.Valid, RationalLogCertificate.check, RationalLogCertificate.Valid, PairedIntegralCertificate.productLower, PairedIntegralCertificate.productUpper, PairedIntegralCertificate.bracketLower, PairedIntegralCertificate.bracketUpper, logSeriesLower, logSeriesUpper, logParameter, Finset.sum_range_succ, tLower, tUpper, uLower, uUpper, a, h, d, mu, K]

theorem row0166_checked : certificate0166.check = true := by
  norm_num [certificate0166, PairedIntegralCertificate.check, PairedIntegralCertificate.Valid, RationalLogCertificate.check, RationalLogCertificate.Valid, PairedIntegralCertificate.productLower, PairedIntegralCertificate.productUpper, PairedIntegralCertificate.bracketLower, PairedIntegralCertificate.bracketUpper, logSeriesLower, logSeriesUpper, logParameter, Finset.sum_range_succ, tLower, tUpper, uLower, uUpper, a, h, d, mu, K]

theorem row0167_checked : certificate0167.check = true := by
  norm_num [certificate0167, PairedIntegralCertificate.check, PairedIntegralCertificate.Valid, RationalLogCertificate.check, RationalLogCertificate.Valid, PairedIntegralCertificate.productLower, PairedIntegralCertificate.productUpper, PairedIntegralCertificate.bracketLower, PairedIntegralCertificate.bracketUpper, logSeriesLower, logSeriesUpper, logParameter, Finset.sum_range_succ, tLower, tUpper, uLower, uUpper, a, h, d, mu, K]

theorem row0168_checked : certificate0168.check = true := by
  norm_num [certificate0168, PairedIntegralCertificate.check, PairedIntegralCertificate.Valid, RationalLogCertificate.check, RationalLogCertificate.Valid, PairedIntegralCertificate.productLower, PairedIntegralCertificate.productUpper, PairedIntegralCertificate.bracketLower, PairedIntegralCertificate.bracketUpper, logSeriesLower, logSeriesUpper, logParameter, Finset.sum_range_succ, tLower, tUpper, uLower, uUpper, a, h, d, mu, K]

theorem row0169_checked : certificate0169.check = true := by
  norm_num [certificate0169, PairedIntegralCertificate.check, PairedIntegralCertificate.Valid, RationalLogCertificate.check, RationalLogCertificate.Valid, PairedIntegralCertificate.productLower, PairedIntegralCertificate.productUpper, PairedIntegralCertificate.bracketLower, PairedIntegralCertificate.bracketUpper, logSeriesLower, logSeriesUpper, logParameter, Finset.sum_range_succ, tLower, tUpper, uLower, uUpper, a, h, d, mu, K]

theorem row0170_checked : certificate0170.check = true := by
  norm_num [certificate0170, PairedIntegralCertificate.check, PairedIntegralCertificate.Valid, RationalLogCertificate.check, RationalLogCertificate.Valid, PairedIntegralCertificate.productLower, PairedIntegralCertificate.productUpper, PairedIntegralCertificate.bracketLower, PairedIntegralCertificate.bracketUpper, logSeriesLower, logSeriesUpper, logParameter, Finset.sum_range_succ, tLower, tUpper, uLower, uUpper, a, h, d, mu, K]

theorem row0171_checked : certificate0171.check = true := by
  norm_num [certificate0171, PairedIntegralCertificate.check, PairedIntegralCertificate.Valid, RationalLogCertificate.check, RationalLogCertificate.Valid, PairedIntegralCertificate.productLower, PairedIntegralCertificate.productUpper, PairedIntegralCertificate.bracketLower, PairedIntegralCertificate.bracketUpper, logSeriesLower, logSeriesUpper, logParameter, Finset.sum_range_succ, tLower, tUpper, uLower, uUpper, a, h, d, mu, K]

theorem row0172_checked : certificate0172.check = true := by
  norm_num [certificate0172, PairedIntegralCertificate.check, PairedIntegralCertificate.Valid, RationalLogCertificate.check, RationalLogCertificate.Valid, PairedIntegralCertificate.productLower, PairedIntegralCertificate.productUpper, PairedIntegralCertificate.bracketLower, PairedIntegralCertificate.bracketUpper, logSeriesLower, logSeriesUpper, logParameter, Finset.sum_range_succ, tLower, tUpper, uLower, uUpper, a, h, d, mu, K]

theorem row0173_checked : certificate0173.check = true := by
  norm_num [certificate0173, PairedIntegralCertificate.check, PairedIntegralCertificate.Valid, RationalLogCertificate.check, RationalLogCertificate.Valid, PairedIntegralCertificate.productLower, PairedIntegralCertificate.productUpper, PairedIntegralCertificate.bracketLower, PairedIntegralCertificate.bracketUpper, logSeriesLower, logSeriesUpper, logParameter, Finset.sum_range_succ, tLower, tUpper, uLower, uUpper, a, h, d, mu, K]

theorem row0174_checked : certificate0174.check = true := by
  norm_num [certificate0174, PairedIntegralCertificate.check, PairedIntegralCertificate.Valid, RationalLogCertificate.check, RationalLogCertificate.Valid, PairedIntegralCertificate.productLower, PairedIntegralCertificate.productUpper, PairedIntegralCertificate.bracketLower, PairedIntegralCertificate.bracketUpper, logSeriesLower, logSeriesUpper, logParameter, Finset.sum_range_succ, tLower, tUpper, uLower, uUpper, a, h, d, mu, K]

theorem row0175_checked : certificate0175.check = true := by
  norm_num [certificate0175, PairedIntegralCertificate.check, PairedIntegralCertificate.Valid, RationalLogCertificate.check, RationalLogCertificate.Valid, PairedIntegralCertificate.productLower, PairedIntegralCertificate.productUpper, PairedIntegralCertificate.bracketLower, PairedIntegralCertificate.bracketUpper, logSeriesLower, logSeriesUpper, logParameter, Finset.sum_range_succ, tLower, tUpper, uLower, uUpper, a, h, d, mu, K]

theorem row0176_checked : certificate0176.check = true := by
  norm_num [certificate0176, PairedIntegralCertificate.check, PairedIntegralCertificate.Valid, RationalLogCertificate.check, RationalLogCertificate.Valid, PairedIntegralCertificate.productLower, PairedIntegralCertificate.productUpper, PairedIntegralCertificate.bracketLower, PairedIntegralCertificate.bracketUpper, logSeriesLower, logSeriesUpper, logParameter, Finset.sum_range_succ, tLower, tUpper, uLower, uUpper, a, h, d, mu, K]

theorem row0177_checked : certificate0177.check = true := by
  norm_num [certificate0177, PairedIntegralCertificate.check, PairedIntegralCertificate.Valid, RationalLogCertificate.check, RationalLogCertificate.Valid, PairedIntegralCertificate.productLower, PairedIntegralCertificate.productUpper, PairedIntegralCertificate.bracketLower, PairedIntegralCertificate.bracketUpper, logSeriesLower, logSeriesUpper, logParameter, Finset.sum_range_succ, tLower, tUpper, uLower, uUpper, a, h, d, mu, K]

theorem row0178_checked : certificate0178.check = true := by
  norm_num [certificate0178, PairedIntegralCertificate.check, PairedIntegralCertificate.Valid, RationalLogCertificate.check, RationalLogCertificate.Valid, PairedIntegralCertificate.productLower, PairedIntegralCertificate.productUpper, PairedIntegralCertificate.bracketLower, PairedIntegralCertificate.bracketUpper, logSeriesLower, logSeriesUpper, logParameter, Finset.sum_range_succ, tLower, tUpper, uLower, uUpper, a, h, d, mu, K]

theorem row0179_checked : certificate0179.check = true := by
  norm_num [certificate0179, PairedIntegralCertificate.check, PairedIntegralCertificate.Valid, RationalLogCertificate.check, RationalLogCertificate.Valid, PairedIntegralCertificate.productLower, PairedIntegralCertificate.productUpper, PairedIntegralCertificate.bracketLower, PairedIntegralCertificate.bracketUpper, logSeriesLower, logSeriesUpper, logParameter, Finset.sum_range_succ, tLower, tUpper, uLower, uUpper, a, h, d, mu, K]

theorem row0180_checked : certificate0180.check = true := by
  norm_num [certificate0180, PairedIntegralCertificate.check, PairedIntegralCertificate.Valid, RationalLogCertificate.check, RationalLogCertificate.Valid, PairedIntegralCertificate.productLower, PairedIntegralCertificate.productUpper, PairedIntegralCertificate.bracketLower, PairedIntegralCertificate.bracketUpper, logSeriesLower, logSeriesUpper, logParameter, Finset.sum_range_succ, tLower, tUpper, uLower, uUpper, a, h, d, mu, K]

theorem row0181_checked : certificate0181.check = true := by
  norm_num [certificate0181, PairedIntegralCertificate.check, PairedIntegralCertificate.Valid, RationalLogCertificate.check, RationalLogCertificate.Valid, PairedIntegralCertificate.productLower, PairedIntegralCertificate.productUpper, PairedIntegralCertificate.bracketLower, PairedIntegralCertificate.bracketUpper, logSeriesLower, logSeriesUpper, logParameter, Finset.sum_range_succ, tLower, tUpper, uLower, uUpper, a, h, d, mu, K]

theorem row0182_checked : certificate0182.check = true := by
  norm_num [certificate0182, PairedIntegralCertificate.check, PairedIntegralCertificate.Valid, RationalLogCertificate.check, RationalLogCertificate.Valid, PairedIntegralCertificate.productLower, PairedIntegralCertificate.productUpper, PairedIntegralCertificate.bracketLower, PairedIntegralCertificate.bracketUpper, logSeriesLower, logSeriesUpper, logParameter, Finset.sum_range_succ, tLower, tUpper, uLower, uUpper, a, h, d, mu, K]

theorem row0183_checked : certificate0183.check = true := by
  norm_num [certificate0183, PairedIntegralCertificate.check, PairedIntegralCertificate.Valid, RationalLogCertificate.check, RationalLogCertificate.Valid, PairedIntegralCertificate.productLower, PairedIntegralCertificate.productUpper, PairedIntegralCertificate.bracketLower, PairedIntegralCertificate.bracketUpper, logSeriesLower, logSeriesUpper, logParameter, Finset.sum_range_succ, tLower, tUpper, uLower, uUpper, a, h, d, mu, K]

theorem row0184_checked : certificate0184.check = true := by
  norm_num [certificate0184, PairedIntegralCertificate.check, PairedIntegralCertificate.Valid, RationalLogCertificate.check, RationalLogCertificate.Valid, PairedIntegralCertificate.productLower, PairedIntegralCertificate.productUpper, PairedIntegralCertificate.bracketLower, PairedIntegralCertificate.bracketUpper, logSeriesLower, logSeriesUpper, logParameter, Finset.sum_range_succ, tLower, tUpper, uLower, uUpper, a, h, d, mu, K]

theorem row0185_checked : certificate0185.check = true := by
  norm_num [certificate0185, PairedIntegralCertificate.check, PairedIntegralCertificate.Valid, RationalLogCertificate.check, RationalLogCertificate.Valid, PairedIntegralCertificate.productLower, PairedIntegralCertificate.productUpper, PairedIntegralCertificate.bracketLower, PairedIntegralCertificate.bracketUpper, logSeriesLower, logSeriesUpper, logParameter, Finset.sum_range_succ, tLower, tUpper, uLower, uUpper, a, h, d, mu, K]

theorem row0186_checked : certificate0186.check = true := by
  norm_num [certificate0186, PairedIntegralCertificate.check, PairedIntegralCertificate.Valid, RationalLogCertificate.check, RationalLogCertificate.Valid, PairedIntegralCertificate.productLower, PairedIntegralCertificate.productUpper, PairedIntegralCertificate.bracketLower, PairedIntegralCertificate.bracketUpper, logSeriesLower, logSeriesUpper, logParameter, Finset.sum_range_succ, tLower, tUpper, uLower, uUpper, a, h, d, mu, K]

theorem row0187_checked : certificate0187.check = true := by
  norm_num [certificate0187, PairedIntegralCertificate.check, PairedIntegralCertificate.Valid, RationalLogCertificate.check, RationalLogCertificate.Valid, PairedIntegralCertificate.productLower, PairedIntegralCertificate.productUpper, PairedIntegralCertificate.bracketLower, PairedIntegralCertificate.bracketUpper, logSeriesLower, logSeriesUpper, logParameter, Finset.sum_range_succ, tLower, tUpper, uLower, uUpper, a, h, d, mu, K]

theorem row0188_checked : certificate0188.check = true := by
  norm_num [certificate0188, PairedIntegralCertificate.check, PairedIntegralCertificate.Valid, RationalLogCertificate.check, RationalLogCertificate.Valid, PairedIntegralCertificate.productLower, PairedIntegralCertificate.productUpper, PairedIntegralCertificate.bracketLower, PairedIntegralCertificate.bracketUpper, logSeriesLower, logSeriesUpper, logParameter, Finset.sum_range_succ, tLower, tUpper, uLower, uUpper, a, h, d, mu, K]

theorem row0189_checked : certificate0189.check = true := by
  norm_num [certificate0189, PairedIntegralCertificate.check, PairedIntegralCertificate.Valid, RationalLogCertificate.check, RationalLogCertificate.Valid, PairedIntegralCertificate.productLower, PairedIntegralCertificate.productUpper, PairedIntegralCertificate.bracketLower, PairedIntegralCertificate.bracketUpper, logSeriesLower, logSeriesUpper, logParameter, Finset.sum_range_succ, tLower, tUpper, uLower, uUpper, a, h, d, mu, K]

theorem row0190_checked : certificate0190.check = true := by
  norm_num [certificate0190, PairedIntegralCertificate.check, PairedIntegralCertificate.Valid, RationalLogCertificate.check, RationalLogCertificate.Valid, PairedIntegralCertificate.productLower, PairedIntegralCertificate.productUpper, PairedIntegralCertificate.bracketLower, PairedIntegralCertificate.bracketUpper, logSeriesLower, logSeriesUpper, logParameter, Finset.sum_range_succ, tLower, tUpper, uLower, uUpper, a, h, d, mu, K]

theorem row0191_checked : certificate0191.check = true := by
  norm_num [certificate0191, PairedIntegralCertificate.check, PairedIntegralCertificate.Valid, RationalLogCertificate.check, RationalLogCertificate.Valid, PairedIntegralCertificate.productLower, PairedIntegralCertificate.productUpper, PairedIntegralCertificate.bracketLower, PairedIntegralCertificate.bracketUpper, logSeriesLower, logSeriesUpper, logParameter, Finset.sum_range_succ, tLower, tUpper, uLower, uUpper, a, h, d, mu, K]

theorem certificates_checked (i : Fin 64) : (certificates i).check = true := by
  fin_cases i
  · exact row0128_checked
  · exact row0129_checked
  · exact row0130_checked
  · exact row0131_checked
  · exact row0132_checked
  · exact row0133_checked
  · exact row0134_checked
  · exact row0135_checked
  · exact row0136_checked
  · exact row0137_checked
  · exact row0138_checked
  · exact row0139_checked
  · exact row0140_checked
  · exact row0141_checked
  · exact row0142_checked
  · exact row0143_checked
  · exact row0144_checked
  · exact row0145_checked
  · exact row0146_checked
  · exact row0147_checked
  · exact row0148_checked
  · exact row0149_checked
  · exact row0150_checked
  · exact row0151_checked
  · exact row0152_checked
  · exact row0153_checked
  · exact row0154_checked
  · exact row0155_checked
  · exact row0156_checked
  · exact row0157_checked
  · exact row0158_checked
  · exact row0159_checked
  · exact row0160_checked
  · exact row0161_checked
  · exact row0162_checked
  · exact row0163_checked
  · exact row0164_checked
  · exact row0165_checked
  · exact row0166_checked
  · exact row0167_checked
  · exact row0168_checked
  · exact row0169_checked
  · exact row0170_checked
  · exact row0171_checked
  · exact row0172_checked
  · exact row0173_checked
  · exact row0174_checked
  · exact row0175_checked
  · exact row0176_checked
  · exact row0177_checked
  · exact row0178_checked
  · exact row0179_checked
  · exact row0180_checked
  · exact row0181_checked
  · exact row0182_checked
  · exact row0183_checked
  · exact row0184_checked
  · exact row0185_checked
  · exact row0186_checked
  · exact row0187_checked
  · exact row0188_checked
  · exact row0189_checked
  · exact row0190_checked
  · exact row0191_checked

theorem geometry_checked (i : Fin 64) :
    E0Geometry (rowIndices i).1 (rowIndices i).2 (rowZ i) := by
  fin_cases i <;>
    norm_num [E0Geometry, rowIndices, rowZ, tLower, tUpper, uLower, uUpper, a, h, d, mu]

theorem certificate_inputs (i : Fin 64) :
    (certificates i).K = K ∧ (certificates i).a = a ∧
      (certificates i).tl = tLower (rowIndices i).1 ∧
      (certificates i).tr = tUpper (rowIndices i).1 ∧
      (certificates i).ul = uLower (rowIndices i).2 ∧
      (certificates i).ur = uUpper (rowIndices i).2 ∧
      (certificates i).Z = rowZ i := by
  fin_cases i <;> norm_num [certificates, rowIndices, rowZ, certificate0128, certificate0129, certificate0130, certificate0131, certificate0132, certificate0133, certificate0134, certificate0135, certificate0136, certificate0137, certificate0138, certificate0139, certificate0140, certificate0141, certificate0142, certificate0143, certificate0144, certificate0145, certificate0146, certificate0147, certificate0148, certificate0149, certificate0150, certificate0151, certificate0152, certificate0153, certificate0154, certificate0155, certificate0156, certificate0157, certificate0158, certificate0159, certificate0160, certificate0161, certificate0162, certificate0163, certificate0164, certificate0165, certificate0166, certificate0167, certificate0168, certificate0169, certificate0170, certificate0171, certificate0172, certificate0173, certificate0174, certificate0175, certificate0176, certificate0177, certificate0178, certificate0179, certificate0180, certificate0181, certificate0182, certificate0183, certificate0184, certificate0185, certificate0186, certificate0187, certificate0188, certificate0189, certificate0190, certificate0191]

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

theorem lower_sum : (∑ i : Fin 64, (certificates i).lower) = lowerBound := by
  norm_num [certificates, lowerBound, Fin.sum_univ_succ, certificate0128, certificate0129, certificate0130, certificate0131, certificate0132, certificate0133, certificate0134, certificate0135, certificate0136, certificate0137, certificate0138, certificate0139, certificate0140, certificate0141, certificate0142, certificate0143, certificate0144, certificate0145, certificate0146, certificate0147, certificate0148, certificate0149, certificate0150, certificate0151, certificate0152, certificate0153, certificate0154, certificate0155, certificate0156, certificate0157, certificate0158, certificate0159, certificate0160, certificate0161, certificate0162, certificate0163, certificate0164, certificate0165, certificate0166, certificate0167, certificate0168, certificate0169, certificate0170, certificate0171, certificate0172, certificate0173, certificate0174, certificate0175, certificate0176, certificate0177, certificate0178, certificate0179, certificate0180, certificate0181, certificate0182, certificate0183, certificate0184, certificate0185, certificate0186, certificate0187, certificate0188, certificate0189, certificate0190, certificate0191]

theorem upper_sum : (∑ i : Fin 64, (certificates i).upper) = upperBound := by
  norm_num [certificates, upperBound, Fin.sum_univ_succ, certificate0128, certificate0129, certificate0130, certificate0131, certificate0132, certificate0133, certificate0134, certificate0135, certificate0136, certificate0137, certificate0138, certificate0139, certificate0140, certificate0141, certificate0142, certificate0143, certificate0144, certificate0145, certificate0146, certificate0147, certificate0148, certificate0149, certificate0150, certificate0151, certificate0152, certificate0153, certificate0154, certificate0155, certificate0156, certificate0157, certificate0158, certificate0159, certificate0160, certificate0161, certificate0162, certificate0163, certificate0164, certificate0165, certificate0166, certificate0167, certificate0168, certificate0169, certificate0170, certificate0171, certificate0172, certificate0173, certificate0174, certificate0175, certificate0176, certificate0177, certificate0178, certificate0179, certificate0180, certificate0181, certificate0182, certificate0183, certificate0184, certificate0185, certificate0186, certificate0187, certificate0188, certificate0189, certificate0190, certificate0191]

/-- Concrete acceptance, checker soundness, and actual-object equality. -/
theorem integral_bounds : (lowerBound : ℝ) ≤ integral ∧ integral ≤ (upperBound : ℝ) := by
  have hs := PairedIntegralCertificate.sum_check_sound Finset.univ certificates
    (fun i _ => certificates_checked i)
  rw [lower_sum, upper_sum] at hs
  simpa only [integral, ← rowIntegral_eq_certificate] using hs

theorem integral_pos : 0 < integral := by
  exact lt_of_lt_of_le (by norm_num [lowerBound]) integral_bounds.1

end ImbalancedChen.Certificates.PairedV2.Batch128To192
