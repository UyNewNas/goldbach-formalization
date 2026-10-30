import ImbalancedChen.Certificates.PairedV2Batch64To128Data
import ImbalancedChen.Certificates.PairedV2Geometry

/-! Byte-identical proof blocks split from the batch to bound compiler memory. -/

namespace ImbalancedChen.Certificates.PairedV2.Batch64To128

open MeasureTheory Set
open scoped BigOperators Interval

set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

theorem certificate_inputs (i : Fin 64) :
    (certificates i).K = K ∧ (certificates i).a = a ∧
      (certificates i).tl = tLower (rowIndices i).1 ∧
      (certificates i).tr = tUpper (rowIndices i).1 ∧
      (certificates i).ul = uLower (rowIndices i).2 ∧
      (certificates i).ur = uUpper (rowIndices i).2 ∧
      (certificates i).Z = rowZ i := by
  fin_cases i <;> norm_num [certificates, rowIndices, rowZ, certificate0064, certificate0065, certificate0066, certificate0067, certificate0068, certificate0069, certificate0070, certificate0071, certificate0072, certificate0073, certificate0074, certificate0075, certificate0076, certificate0077, certificate0078, certificate0079, certificate0080, certificate0081, certificate0082, certificate0083, certificate0084, certificate0085, certificate0086, certificate0087, certificate0088, certificate0089, certificate0090, certificate0091, certificate0092, certificate0093, certificate0094, certificate0095, certificate0096, certificate0097, certificate0098, certificate0099, certificate0100, certificate0101, certificate0102, certificate0103, certificate0104, certificate0105, certificate0106, certificate0107, certificate0108, certificate0109, certificate0110, certificate0111, certificate0112, certificate0113, certificate0114, certificate0115, certificate0116, certificate0117, certificate0118, certificate0119, certificate0120, certificate0121, certificate0122, certificate0123, certificate0124, certificate0125, certificate0126, certificate0127]

end ImbalancedChen.Certificates.PairedV2.Batch64To128
