import ImbalancedChen.Certificates.PairedV2Batch64To128Data
import ImbalancedChen.Certificates.PairedV2Geometry

/-! Byte-identical proof blocks split from the batch to bound compiler memory. -/

namespace ImbalancedChen.Certificates.PairedV2.Batch64To128

open MeasureTheory Set
open scoped BigOperators Interval

set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

theorem row0064_checked : certificate0064.check = true := by
  norm_num [certificate0064, PairedIntegralCertificate.check, PairedIntegralCertificate.Valid, RationalLogCertificate.check, RationalLogCertificate.Valid, PairedIntegralCertificate.productLower, PairedIntegralCertificate.productUpper, PairedIntegralCertificate.bracketLower, PairedIntegralCertificate.bracketUpper, logSeriesLower, logSeriesUpper, logParameter, Finset.sum_range_succ, tLower, tUpper, uLower, uUpper, a, h, d, mu, K]

theorem row0065_checked : certificate0065.check = true := by
  norm_num [certificate0065, PairedIntegralCertificate.check, PairedIntegralCertificate.Valid, RationalLogCertificate.check, RationalLogCertificate.Valid, PairedIntegralCertificate.productLower, PairedIntegralCertificate.productUpper, PairedIntegralCertificate.bracketLower, PairedIntegralCertificate.bracketUpper, logSeriesLower, logSeriesUpper, logParameter, Finset.sum_range_succ, tLower, tUpper, uLower, uUpper, a, h, d, mu, K]

theorem row0066_checked : certificate0066.check = true := by
  norm_num [certificate0066, PairedIntegralCertificate.check, PairedIntegralCertificate.Valid, RationalLogCertificate.check, RationalLogCertificate.Valid, PairedIntegralCertificate.productLower, PairedIntegralCertificate.productUpper, PairedIntegralCertificate.bracketLower, PairedIntegralCertificate.bracketUpper, logSeriesLower, logSeriesUpper, logParameter, Finset.sum_range_succ, tLower, tUpper, uLower, uUpper, a, h, d, mu, K]

theorem row0067_checked : certificate0067.check = true := by
  norm_num [certificate0067, PairedIntegralCertificate.check, PairedIntegralCertificate.Valid, RationalLogCertificate.check, RationalLogCertificate.Valid, PairedIntegralCertificate.productLower, PairedIntegralCertificate.productUpper, PairedIntegralCertificate.bracketLower, PairedIntegralCertificate.bracketUpper, logSeriesLower, logSeriesUpper, logParameter, Finset.sum_range_succ, tLower, tUpper, uLower, uUpper, a, h, d, mu, K]

theorem row0068_checked : certificate0068.check = true := by
  norm_num [certificate0068, PairedIntegralCertificate.check, PairedIntegralCertificate.Valid, RationalLogCertificate.check, RationalLogCertificate.Valid, PairedIntegralCertificate.productLower, PairedIntegralCertificate.productUpper, PairedIntegralCertificate.bracketLower, PairedIntegralCertificate.bracketUpper, logSeriesLower, logSeriesUpper, logParameter, Finset.sum_range_succ, tLower, tUpper, uLower, uUpper, a, h, d, mu, K]

theorem row0069_checked : certificate0069.check = true := by
  norm_num [certificate0069, PairedIntegralCertificate.check, PairedIntegralCertificate.Valid, RationalLogCertificate.check, RationalLogCertificate.Valid, PairedIntegralCertificate.productLower, PairedIntegralCertificate.productUpper, PairedIntegralCertificate.bracketLower, PairedIntegralCertificate.bracketUpper, logSeriesLower, logSeriesUpper, logParameter, Finset.sum_range_succ, tLower, tUpper, uLower, uUpper, a, h, d, mu, K]

theorem row0070_checked : certificate0070.check = true := by
  norm_num [certificate0070, PairedIntegralCertificate.check, PairedIntegralCertificate.Valid, RationalLogCertificate.check, RationalLogCertificate.Valid, PairedIntegralCertificate.productLower, PairedIntegralCertificate.productUpper, PairedIntegralCertificate.bracketLower, PairedIntegralCertificate.bracketUpper, logSeriesLower, logSeriesUpper, logParameter, Finset.sum_range_succ, tLower, tUpper, uLower, uUpper, a, h, d, mu, K]

theorem row0071_checked : certificate0071.check = true := by
  norm_num [certificate0071, PairedIntegralCertificate.check, PairedIntegralCertificate.Valid, RationalLogCertificate.check, RationalLogCertificate.Valid, PairedIntegralCertificate.productLower, PairedIntegralCertificate.productUpper, PairedIntegralCertificate.bracketLower, PairedIntegralCertificate.bracketUpper, logSeriesLower, logSeriesUpper, logParameter, Finset.sum_range_succ, tLower, tUpper, uLower, uUpper, a, h, d, mu, K]

end ImbalancedChen.Certificates.PairedV2.Batch64To128
