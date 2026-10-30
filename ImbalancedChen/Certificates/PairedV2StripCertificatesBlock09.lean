import ImbalancedChen.Certificates.PairedV2StripCertificate470
import ImbalancedChen.Certificates.PairedV2StripCertificate471
import ImbalancedChen.Certificates.PairedV2StripCertificate472
import ImbalancedChen.Certificates.PairedV2StripCertificate473
import ImbalancedChen.Certificates.PairedV2StripCertificate474
import ImbalancedChen.Certificates.PairedV2StripCertificate475
import ImbalancedChen.Certificates.PairedV2StripCertificate476
import ImbalancedChen.Certificates.PairedV2StripCertificate477
import ImbalancedChen.Certificates.PairedV2StripCertificate478
import ImbalancedChen.Certificates.PairedV2StripCertificate479
import ImbalancedChen.Certificates.PairedV2StripCertificate480
import ImbalancedChen.Certificates.PairedV2StripCertificate481
import ImbalancedChen.Certificates.PairedV2StripCertificate482
import ImbalancedChen.Certificates.PairedV2StripCertificate483
import ImbalancedChen.Certificates.PairedV2StripCertificate484
import ImbalancedChen.Certificates.PairedV2StripCertificate485

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Bounded composition of the original strip checks, with no new check assumption. -/
theorem stripBlock09_checked (k : Fin 16) :
    StripAssembly.StripChecked (StripAssembly.indexBlock09 k) := by
  fin_cases k
  · exact strip470_checked
  · exact strip471_checked
  · exact strip472_checked
  · exact strip473_checked
  · exact strip474_checked
  · exact strip475_checked
  · exact strip476_checked
  · exact strip477_checked
  · exact strip478_checked
  · exact strip479_checked
  · exact strip480_checked
  · exact strip481_checked
  · exact strip482_checked
  · exact strip483_checked
  · exact strip484_checked
  · exact strip485_checked

end ImbalancedChen.Certificates.PairedV2.FullMask
