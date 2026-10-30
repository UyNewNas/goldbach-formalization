import ImbalancedChen.Certificates.PairedV2StripCertificate454
import ImbalancedChen.Certificates.PairedV2StripCertificate455
import ImbalancedChen.Certificates.PairedV2StripCertificate456
import ImbalancedChen.Certificates.PairedV2StripCertificate457
import ImbalancedChen.Certificates.PairedV2StripCertificate458
import ImbalancedChen.Certificates.PairedV2StripCertificate459
import ImbalancedChen.Certificates.PairedV2StripCertificate460
import ImbalancedChen.Certificates.PairedV2StripCertificate461
import ImbalancedChen.Certificates.PairedV2StripCertificate462
import ImbalancedChen.Certificates.PairedV2StripCertificate463
import ImbalancedChen.Certificates.PairedV2StripCertificate464
import ImbalancedChen.Certificates.PairedV2StripCertificate465
import ImbalancedChen.Certificates.PairedV2StripCertificate466
import ImbalancedChen.Certificates.PairedV2StripCertificate467
import ImbalancedChen.Certificates.PairedV2StripCertificate468
import ImbalancedChen.Certificates.PairedV2StripCertificate469

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Bounded composition of the original strip checks, with no new check assumption. -/
theorem stripBlock08_checked (k : Fin 16) :
    StripAssembly.StripChecked (StripAssembly.indexBlock08 k) := by
  fin_cases k
  · exact strip454_checked
  · exact strip455_checked
  · exact strip456_checked
  · exact strip457_checked
  · exact strip458_checked
  · exact strip459_checked
  · exact strip460_checked
  · exact strip461_checked
  · exact strip462_checked
  · exact strip463_checked
  · exact strip464_checked
  · exact strip465_checked
  · exact strip466_checked
  · exact strip467_checked
  · exact strip468_checked
  · exact strip469_checked

end ImbalancedChen.Certificates.PairedV2.FullMask
