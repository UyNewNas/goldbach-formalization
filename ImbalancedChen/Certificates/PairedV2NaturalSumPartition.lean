import ImbalancedChen.Certificates.PairedV2FullCertificateData
import Mathlib.Data.List.OfFn
import ImbalancedChen.Certificates.PairedV2NaturalSumsBlock00
import ImbalancedChen.Certificates.PairedV2NaturalSumsBlock01
import ImbalancedChen.Certificates.PairedV2NaturalSumsBlock02
import ImbalancedChen.Certificates.PairedV2NaturalSumsBlock03
import ImbalancedChen.Certificates.PairedV2NaturalSumsBlock04
import ImbalancedChen.Certificates.PairedV2NaturalSumsBlock05
import ImbalancedChen.Certificates.PairedV2NaturalSumsBlock06
import ImbalancedChen.Certificates.PairedV2NaturalSumsBlock07
import ImbalancedChen.Certificates.PairedV2NaturalSumsBlock08
import ImbalancedChen.Certificates.PairedV2NaturalSumsBlock09
import ImbalancedChen.Certificates.PairedV2NaturalSumsBlock10
import ImbalancedChen.Certificates.PairedV2NaturalSumsBlock11

/-! Original ordered partition, moved verbatim before the length/Row bridges. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask.NaturalSums

open scoped BigOperators

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- All 186 strips in their original order, grouped only for proof assembly. -/
def blocks : List (List (List Approximation)) :=
  [block00, block01, block02, block03, block04, block05, block06, block07, block08, block09, block10, block11]

/-- Definitional identity, with no numerical or source-ordinal sampling. -/
theorem approximations_partition : List.ofFn approximations = blocks.flatten := by
  rfl

end ImbalancedChen.Certificates.PairedV2.FullMask.NaturalSums
