import ImbalancedChen.Certificates.PairedV2StripCertificate326
import ImbalancedChen.Certificates.PairedV2StripCertificate327
import ImbalancedChen.Certificates.PairedV2StripCertificate328
import ImbalancedChen.Certificates.PairedV2StripCertificate329
import ImbalancedChen.Certificates.PairedV2StripCertificate330
import ImbalancedChen.Certificates.PairedV2StripCertificate331
import ImbalancedChen.Certificates.PairedV2StripCertificate332
import ImbalancedChen.Certificates.PairedV2StripCertificate333
import ImbalancedChen.Certificates.PairedV2StripCertificate334
import ImbalancedChen.Certificates.PairedV2StripCertificate335
import ImbalancedChen.Certificates.PairedV2StripCertificate336
import ImbalancedChen.Certificates.PairedV2StripCertificate337
import ImbalancedChen.Certificates.PairedV2StripCertificate338
import ImbalancedChen.Certificates.PairedV2StripCertificate339
import ImbalancedChen.Certificates.PairedV2StripCertificate340
import ImbalancedChen.Certificates.PairedV2StripCertificate341

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Bounded composition of the original strip checks, with no new check assumption. -/
theorem stripBlock00_checked (k : Fin 16) :
    StripAssembly.StripChecked (StripAssembly.indexBlock00 k) := by
  fin_cases k
  · exact strip326_checked
  · exact strip327_checked
  · exact strip328_checked
  · exact strip329_checked
  · exact strip330_checked
  · exact strip331_checked
  · exact strip332_checked
  · exact strip333_checked
  · exact strip334_checked
  · exact strip335_checked
  · exact strip336_checked
  · exact strip337_checked
  · exact strip338_checked
  · exact strip339_checked
  · exact strip340_checked
  · exact strip341_checked

end ImbalancedChen.Certificates.PairedV2.FullMask
