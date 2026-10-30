import ImbalancedChen.Certificates.PairedV2Batch4To64Data
import ImbalancedChen.Certificates.PairedV2Geometry

/-! Byte-identical proof blocks split from the batch to bound compiler memory. -/

namespace ImbalancedChen.Certificates.PairedV2.Batch4To64

open MeasureTheory Set
open scoped BigOperators Interval

set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

theorem row0060_checked : certificate0060.check = true := by
  norm_num [certificate0060, PairedIntegralCertificate.check, PairedIntegralCertificate.Valid, RationalLogCertificate.check, RationalLogCertificate.Valid, PairedIntegralCertificate.productLower, PairedIntegralCertificate.productUpper, PairedIntegralCertificate.bracketLower, PairedIntegralCertificate.bracketUpper, logSeriesLower, logSeriesUpper, logParameter, Finset.sum_range_succ, tLower, tUpper, uLower, uUpper, a, h, d, mu, K]

theorem row0061_checked : certificate0061.check = true := by
  norm_num [certificate0061, PairedIntegralCertificate.check, PairedIntegralCertificate.Valid, RationalLogCertificate.check, RationalLogCertificate.Valid, PairedIntegralCertificate.productLower, PairedIntegralCertificate.productUpper, PairedIntegralCertificate.bracketLower, PairedIntegralCertificate.bracketUpper, logSeriesLower, logSeriesUpper, logParameter, Finset.sum_range_succ, tLower, tUpper, uLower, uUpper, a, h, d, mu, K]

theorem row0062_checked : certificate0062.check = true := by
  norm_num [certificate0062, PairedIntegralCertificate.check, PairedIntegralCertificate.Valid, RationalLogCertificate.check, RationalLogCertificate.Valid, PairedIntegralCertificate.productLower, PairedIntegralCertificate.productUpper, PairedIntegralCertificate.bracketLower, PairedIntegralCertificate.bracketUpper, logSeriesLower, logSeriesUpper, logParameter, Finset.sum_range_succ, tLower, tUpper, uLower, uUpper, a, h, d, mu, K]

theorem row0063_checked : certificate0063.check = true := by
  norm_num [certificate0063, PairedIntegralCertificate.check, PairedIntegralCertificate.Valid, RationalLogCertificate.check, RationalLogCertificate.Valid, PairedIntegralCertificate.productLower, PairedIntegralCertificate.productUpper, PairedIntegralCertificate.bracketLower, PairedIntegralCertificate.bracketUpper, logSeriesLower, logSeriesUpper, logParameter, Finset.sum_range_succ, tLower, tUpper, uLower, uUpper, a, h, d, mu, K]

end ImbalancedChen.Certificates.PairedV2.Batch4To64
