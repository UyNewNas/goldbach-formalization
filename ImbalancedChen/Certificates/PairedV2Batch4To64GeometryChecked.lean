import ImbalancedChen.Certificates.PairedV2Batch4To64Data
import ImbalancedChen.Certificates.PairedV2Geometry

/-! Byte-identical proof blocks split from the batch to bound compiler memory. -/

namespace ImbalancedChen.Certificates.PairedV2.Batch4To64

open MeasureTheory Set
open scoped BigOperators Interval

set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

theorem geometry_checked (i : Fin 60) :
    E0Geometry (rowIndices i).1 (rowIndices i).2 (rowZ i) := by
  fin_cases i <;>
    norm_num [E0Geometry, rowIndices, rowZ, tLower, tUpper, uLower, uUpper, a, h, d, mu]

end ImbalancedChen.Certificates.PairedV2.Batch4To64
