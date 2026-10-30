import ImbalancedChen.Certificates.PairedV2StripCertificate406
import ImbalancedChen.Certificates.PairedV2StripCertificate407
import ImbalancedChen.Certificates.PairedV2StripCertificate408
import ImbalancedChen.Certificates.PairedV2StripCertificate409
import ImbalancedChen.Certificates.PairedV2StripCertificate410
import ImbalancedChen.Certificates.PairedV2StripCertificate411
import ImbalancedChen.Certificates.PairedV2StripCertificate412
import ImbalancedChen.Certificates.PairedV2StripCertificate413
import ImbalancedChen.Certificates.PairedV2StripCertificate414
import ImbalancedChen.Certificates.PairedV2StripCertificate415
import ImbalancedChen.Certificates.PairedV2StripCertificate416
import ImbalancedChen.Certificates.PairedV2StripCertificate417
import ImbalancedChen.Certificates.PairedV2StripCertificate418
import ImbalancedChen.Certificates.PairedV2StripCertificate419
import ImbalancedChen.Certificates.PairedV2StripCertificate420
import ImbalancedChen.Certificates.PairedV2StripCertificate421

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Bounded composition of the original strip checks, with no new check assumption. -/
theorem stripBlock05_checked (k : Fin 16) :
    StripAssembly.StripChecked (StripAssembly.indexBlock05 k) := by
  fin_cases k
  · exact strip406_checked
  · exact strip407_checked
  · exact strip408_checked
  · exact strip409_checked
  · exact strip410_checked
  · exact strip411_checked
  · exact strip412_checked
  · exact strip413_checked
  · exact strip414_checked
  · exact strip415_checked
  · exact strip416_checked
  · exact strip417_checked
  · exact strip418_checked
  · exact strip419_checked
  · exact strip420_checked
  · exact strip421_checked

end ImbalancedChen.Certificates.PairedV2.FullMask
