import ImbalancedChen.Certificates.PairedV2Batch4To64Data
import ImbalancedChen.Certificates.PairedV2Geometry

/-! Byte-identical proof blocks split from the batch to bound compiler memory. -/

namespace ImbalancedChen.Certificates.PairedV2.Batch4To64

open MeasureTheory Set
open scoped BigOperators Interval

set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

theorem row0028_checked : certificate0028.check = true := by
  norm_num [certificate0028, PairedIntegralCertificate.check, PairedIntegralCertificate.Valid, RationalLogCertificate.check, RationalLogCertificate.Valid, PairedIntegralCertificate.productLower, PairedIntegralCertificate.productUpper, PairedIntegralCertificate.bracketLower, PairedIntegralCertificate.bracketUpper, logSeriesLower, logSeriesUpper, logParameter, Finset.sum_range_succ, tLower, tUpper, uLower, uUpper, a, h, d, mu, K]

theorem row0029_checked : certificate0029.check = true := by
  norm_num [certificate0029, PairedIntegralCertificate.check, PairedIntegralCertificate.Valid, RationalLogCertificate.check, RationalLogCertificate.Valid, PairedIntegralCertificate.productLower, PairedIntegralCertificate.productUpper, PairedIntegralCertificate.bracketLower, PairedIntegralCertificate.bracketUpper, logSeriesLower, logSeriesUpper, logParameter, Finset.sum_range_succ, tLower, tUpper, uLower, uUpper, a, h, d, mu, K]

theorem row0030_checked : certificate0030.check = true := by
  norm_num [certificate0030, PairedIntegralCertificate.check, PairedIntegralCertificate.Valid, RationalLogCertificate.check, RationalLogCertificate.Valid, PairedIntegralCertificate.productLower, PairedIntegralCertificate.productUpper, PairedIntegralCertificate.bracketLower, PairedIntegralCertificate.bracketUpper, logSeriesLower, logSeriesUpper, logParameter, Finset.sum_range_succ, tLower, tUpper, uLower, uUpper, a, h, d, mu, K]

theorem row0031_checked : certificate0031.check = true := by
  norm_num [certificate0031, PairedIntegralCertificate.check, PairedIntegralCertificate.Valid, RationalLogCertificate.check, RationalLogCertificate.Valid, PairedIntegralCertificate.productLower, PairedIntegralCertificate.productUpper, PairedIntegralCertificate.bracketLower, PairedIntegralCertificate.bracketUpper, logSeriesLower, logSeriesUpper, logParameter, Finset.sum_range_succ, tLower, tUpper, uLower, uUpper, a, h, d, mu, K]

theorem row0032_checked : certificate0032.check = true := by
  norm_num [certificate0032, PairedIntegralCertificate.check, PairedIntegralCertificate.Valid, RationalLogCertificate.check, RationalLogCertificate.Valid, PairedIntegralCertificate.productLower, PairedIntegralCertificate.productUpper, PairedIntegralCertificate.bracketLower, PairedIntegralCertificate.bracketUpper, logSeriesLower, logSeriesUpper, logParameter, Finset.sum_range_succ, tLower, tUpper, uLower, uUpper, a, h, d, mu, K]

theorem row0033_checked : certificate0033.check = true := by
  norm_num [certificate0033, PairedIntegralCertificate.check, PairedIntegralCertificate.Valid, RationalLogCertificate.check, RationalLogCertificate.Valid, PairedIntegralCertificate.productLower, PairedIntegralCertificate.productUpper, PairedIntegralCertificate.bracketLower, PairedIntegralCertificate.bracketUpper, logSeriesLower, logSeriesUpper, logParameter, Finset.sum_range_succ, tLower, tUpper, uLower, uUpper, a, h, d, mu, K]

theorem row0034_checked : certificate0034.check = true := by
  norm_num [certificate0034, PairedIntegralCertificate.check, PairedIntegralCertificate.Valid, RationalLogCertificate.check, RationalLogCertificate.Valid, PairedIntegralCertificate.productLower, PairedIntegralCertificate.productUpper, PairedIntegralCertificate.bracketLower, PairedIntegralCertificate.bracketUpper, logSeriesLower, logSeriesUpper, logParameter, Finset.sum_range_succ, tLower, tUpper, uLower, uUpper, a, h, d, mu, K]

theorem row0035_checked : certificate0035.check = true := by
  norm_num [certificate0035, PairedIntegralCertificate.check, PairedIntegralCertificate.Valid, RationalLogCertificate.check, RationalLogCertificate.Valid, PairedIntegralCertificate.productLower, PairedIntegralCertificate.productUpper, PairedIntegralCertificate.bracketLower, PairedIntegralCertificate.bracketUpper, logSeriesLower, logSeriesUpper, logParameter, Finset.sum_range_succ, tLower, tUpper, uLower, uUpper, a, h, d, mu, K]

end ImbalancedChen.Certificates.PairedV2.Batch4To64
