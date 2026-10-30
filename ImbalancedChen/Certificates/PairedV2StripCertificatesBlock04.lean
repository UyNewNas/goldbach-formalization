import ImbalancedChen.Certificates.PairedV2StripCertificate390
import ImbalancedChen.Certificates.PairedV2StripCertificate391
import ImbalancedChen.Certificates.PairedV2StripCertificate392
import ImbalancedChen.Certificates.PairedV2StripCertificate393
import ImbalancedChen.Certificates.PairedV2StripCertificate394
import ImbalancedChen.Certificates.PairedV2StripCertificate395
import ImbalancedChen.Certificates.PairedV2StripCertificate396
import ImbalancedChen.Certificates.PairedV2StripCertificate397
import ImbalancedChen.Certificates.PairedV2StripCertificate398
import ImbalancedChen.Certificates.PairedV2StripCertificate399
import ImbalancedChen.Certificates.PairedV2StripCertificate400
import ImbalancedChen.Certificates.PairedV2StripCertificate401
import ImbalancedChen.Certificates.PairedV2StripCertificate402
import ImbalancedChen.Certificates.PairedV2StripCertificate403
import ImbalancedChen.Certificates.PairedV2StripCertificate404
import ImbalancedChen.Certificates.PairedV2StripCertificate405

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Bounded composition of the original strip checks, with no new check assumption. -/
theorem stripBlock04_checked (k : Fin 16) :
    StripAssembly.StripChecked (StripAssembly.indexBlock04 k) := by
  fin_cases k
  · exact strip390_checked
  · exact strip391_checked
  · exact strip392_checked
  · exact strip393_checked
  · exact strip394_checked
  · exact strip395_checked
  · exact strip396_checked
  · exact strip397_checked
  · exact strip398_checked
  · exact strip399_checked
  · exact strip400_checked
  · exact strip401_checked
  · exact strip402_checked
  · exact strip403_checked
  · exact strip404_checked
  · exact strip405_checked

end ImbalancedChen.Certificates.PairedV2.FullMask
