import ImbalancedChen.Certificates.PairedV2StripCertificate502
import ImbalancedChen.Certificates.PairedV2StripCertificate503
import ImbalancedChen.Certificates.PairedV2StripCertificate504
import ImbalancedChen.Certificates.PairedV2StripCertificate505
import ImbalancedChen.Certificates.PairedV2StripCertificate506
import ImbalancedChen.Certificates.PairedV2StripCertificate507
import ImbalancedChen.Certificates.PairedV2StripCertificate508
import ImbalancedChen.Certificates.PairedV2StripCertificate509
import ImbalancedChen.Certificates.PairedV2StripCertificate510
import ImbalancedChen.Certificates.PairedV2StripCertificate511
import ImbalancedChen.Certificates.PairedV2StripCertificatesAssemblyCore

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Bounded composition of the original strip checks, with no new check assumption. -/
theorem stripBlock11_checked (k : Fin 10) :
    StripAssembly.StripChecked (StripAssembly.indexBlock11 k) := by
  fin_cases k
  · exact strip502_checked
  · exact strip503_checked
  · exact strip504_checked
  · exact strip505_checked
  · exact strip506_checked
  · exact strip507_checked
  · exact strip508_checked
  · exact strip509_checked
  · exact strip510_checked
  · exact strip511_checked

end ImbalancedChen.Certificates.PairedV2.FullMask
