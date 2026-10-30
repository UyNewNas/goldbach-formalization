import ImbalancedChen.Certificates.PairedV2Batch64To128Data
import ImbalancedChen.Certificates.PairedV2Geometry

/-! Byte-identical proof blocks split from the batch to bound compiler memory. -/

namespace ImbalancedChen.Certificates.PairedV2.Batch64To128

open MeasureTheory Set
open scoped BigOperators Interval

set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

theorem row0104_checked : certificate0104.check = true := by
  norm_num [certificate0104, PairedIntegralCertificate.check, PairedIntegralCertificate.Valid, RationalLogCertificate.check, RationalLogCertificate.Valid, PairedIntegralCertificate.productLower, PairedIntegralCertificate.productUpper, PairedIntegralCertificate.bracketLower, PairedIntegralCertificate.bracketUpper, logSeriesLower, logSeriesUpper, logParameter, Finset.sum_range_succ, tLower, tUpper, uLower, uUpper, a, h, d, mu, K]

theorem row0105_checked : certificate0105.check = true := by
  norm_num [certificate0105, PairedIntegralCertificate.check, PairedIntegralCertificate.Valid, RationalLogCertificate.check, RationalLogCertificate.Valid, PairedIntegralCertificate.productLower, PairedIntegralCertificate.productUpper, PairedIntegralCertificate.bracketLower, PairedIntegralCertificate.bracketUpper, logSeriesLower, logSeriesUpper, logParameter, Finset.sum_range_succ, tLower, tUpper, uLower, uUpper, a, h, d, mu, K]

theorem row0106_checked : certificate0106.check = true := by
  norm_num [certificate0106, PairedIntegralCertificate.check, PairedIntegralCertificate.Valid, RationalLogCertificate.check, RationalLogCertificate.Valid, PairedIntegralCertificate.productLower, PairedIntegralCertificate.productUpper, PairedIntegralCertificate.bracketLower, PairedIntegralCertificate.bracketUpper, logSeriesLower, logSeriesUpper, logParameter, Finset.sum_range_succ, tLower, tUpper, uLower, uUpper, a, h, d, mu, K]

theorem row0107_checked : certificate0107.check = true := by
  norm_num [certificate0107, PairedIntegralCertificate.check, PairedIntegralCertificate.Valid, RationalLogCertificate.check, RationalLogCertificate.Valid, PairedIntegralCertificate.productLower, PairedIntegralCertificate.productUpper, PairedIntegralCertificate.bracketLower, PairedIntegralCertificate.bracketUpper, logSeriesLower, logSeriesUpper, logParameter, Finset.sum_range_succ, tLower, tUpper, uLower, uUpper, a, h, d, mu, K]

theorem row0108_checked : certificate0108.check = true := by
  norm_num [certificate0108, PairedIntegralCertificate.check, PairedIntegralCertificate.Valid, RationalLogCertificate.check, RationalLogCertificate.Valid, PairedIntegralCertificate.productLower, PairedIntegralCertificate.productUpper, PairedIntegralCertificate.bracketLower, PairedIntegralCertificate.bracketUpper, logSeriesLower, logSeriesUpper, logParameter, Finset.sum_range_succ, tLower, tUpper, uLower, uUpper, a, h, d, mu, K]

theorem row0109_checked : certificate0109.check = true := by
  norm_num [certificate0109, PairedIntegralCertificate.check, PairedIntegralCertificate.Valid, RationalLogCertificate.check, RationalLogCertificate.Valid, PairedIntegralCertificate.productLower, PairedIntegralCertificate.productUpper, PairedIntegralCertificate.bracketLower, PairedIntegralCertificate.bracketUpper, logSeriesLower, logSeriesUpper, logParameter, Finset.sum_range_succ, tLower, tUpper, uLower, uUpper, a, h, d, mu, K]

theorem row0110_checked : certificate0110.check = true := by
  norm_num [certificate0110, PairedIntegralCertificate.check, PairedIntegralCertificate.Valid, RationalLogCertificate.check, RationalLogCertificate.Valid, PairedIntegralCertificate.productLower, PairedIntegralCertificate.productUpper, PairedIntegralCertificate.bracketLower, PairedIntegralCertificate.bracketUpper, logSeriesLower, logSeriesUpper, logParameter, Finset.sum_range_succ, tLower, tUpper, uLower, uUpper, a, h, d, mu, K]

theorem row0111_checked : certificate0111.check = true := by
  norm_num [certificate0111, PairedIntegralCertificate.check, PairedIntegralCertificate.Valid, RationalLogCertificate.check, RationalLogCertificate.Valid, PairedIntegralCertificate.productLower, PairedIntegralCertificate.productUpper, PairedIntegralCertificate.bracketLower, PairedIntegralCertificate.bracketUpper, logSeriesLower, logSeriesUpper, logParameter, Finset.sum_range_succ, tLower, tUpper, uLower, uUpper, a, h, d, mu, K]

end ImbalancedChen.Certificates.PairedV2.Batch64To128
