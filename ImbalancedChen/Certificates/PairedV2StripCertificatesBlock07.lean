import ImbalancedChen.Certificates.PairedV2StripCertificate438
import ImbalancedChen.Certificates.PairedV2StripCertificate439
import ImbalancedChen.Certificates.PairedV2StripCertificate440
import ImbalancedChen.Certificates.PairedV2StripCertificate441
import ImbalancedChen.Certificates.PairedV2StripCertificate442
import ImbalancedChen.Certificates.PairedV2StripCertificate443
import ImbalancedChen.Certificates.PairedV2StripCertificate444
import ImbalancedChen.Certificates.PairedV2StripCertificate445
import ImbalancedChen.Certificates.PairedV2StripCertificate446
import ImbalancedChen.Certificates.PairedV2StripCertificate447
import ImbalancedChen.Certificates.PairedV2StripCertificate448
import ImbalancedChen.Certificates.PairedV2StripCertificate449
import ImbalancedChen.Certificates.PairedV2StripCertificate450
import ImbalancedChen.Certificates.PairedV2StripCertificate451
import ImbalancedChen.Certificates.PairedV2StripCertificate452
import ImbalancedChen.Certificates.PairedV2StripCertificate453

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Bounded composition of the original strip checks, with no new check assumption. -/
theorem stripBlock07_checked (k : Fin 16) :
    StripAssembly.StripChecked (StripAssembly.indexBlock07 k) := by
  fin_cases k
  · exact strip438_checked
  · exact strip439_checked
  · exact strip440_checked
  · exact strip441_checked
  · exact strip442_checked
  · exact strip443_checked
  · exact strip444_checked
  · exact strip445_checked
  · exact strip446_checked
  · exact strip447_checked
  · exact strip448_checked
  · exact strip449_checked
  · exact strip450_checked
  · exact strip451_checked
  · exact strip452_checked
  · exact strip453_checked

end ImbalancedChen.Certificates.PairedV2.FullMask
