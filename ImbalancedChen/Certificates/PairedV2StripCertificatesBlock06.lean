import ImbalancedChen.Certificates.PairedV2StripCertificate422
import ImbalancedChen.Certificates.PairedV2StripCertificate423
import ImbalancedChen.Certificates.PairedV2StripCertificate424
import ImbalancedChen.Certificates.PairedV2StripCertificate425
import ImbalancedChen.Certificates.PairedV2StripCertificate426
import ImbalancedChen.Certificates.PairedV2StripCertificate427
import ImbalancedChen.Certificates.PairedV2StripCertificate428
import ImbalancedChen.Certificates.PairedV2StripCertificate429
import ImbalancedChen.Certificates.PairedV2StripCertificate430
import ImbalancedChen.Certificates.PairedV2StripCertificate431
import ImbalancedChen.Certificates.PairedV2StripCertificate432
import ImbalancedChen.Certificates.PairedV2StripCertificate433
import ImbalancedChen.Certificates.PairedV2StripCertificate434
import ImbalancedChen.Certificates.PairedV2StripCertificate435
import ImbalancedChen.Certificates.PairedV2StripCertificate436
import ImbalancedChen.Certificates.PairedV2StripCertificate437

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Bounded composition of the original strip checks, with no new check assumption. -/
theorem stripBlock06_checked (k : Fin 16) :
    StripAssembly.StripChecked (StripAssembly.indexBlock06 k) := by
  fin_cases k
  · exact strip422_checked
  · exact strip423_checked
  · exact strip424_checked
  · exact strip425_checked
  · exact strip426_checked
  · exact strip427_checked
  · exact strip428_checked
  · exact strip429_checked
  · exact strip430_checked
  · exact strip431_checked
  · exact strip432_checked
  · exact strip433_checked
  · exact strip434_checked
  · exact strip435_checked
  · exact strip436_checked
  · exact strip437_checked

end ImbalancedChen.Certificates.PairedV2.FullMask
