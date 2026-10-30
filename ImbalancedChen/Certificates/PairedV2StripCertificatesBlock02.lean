import ImbalancedChen.Certificates.PairedV2StripCertificate358
import ImbalancedChen.Certificates.PairedV2StripCertificate359
import ImbalancedChen.Certificates.PairedV2StripCertificate360
import ImbalancedChen.Certificates.PairedV2StripCertificate361
import ImbalancedChen.Certificates.PairedV2StripCertificate362
import ImbalancedChen.Certificates.PairedV2StripCertificate363
import ImbalancedChen.Certificates.PairedV2StripCertificate364
import ImbalancedChen.Certificates.PairedV2StripCertificate365
import ImbalancedChen.Certificates.PairedV2StripCertificate366
import ImbalancedChen.Certificates.PairedV2StripCertificate367
import ImbalancedChen.Certificates.PairedV2StripCertificate368
import ImbalancedChen.Certificates.PairedV2StripCertificate369
import ImbalancedChen.Certificates.PairedV2StripCertificate370
import ImbalancedChen.Certificates.PairedV2StripCertificate371
import ImbalancedChen.Certificates.PairedV2StripCertificate372
import ImbalancedChen.Certificates.PairedV2StripCertificate373

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Bounded composition of the original strip checks, with no new check assumption. -/
theorem stripBlock02_checked (k : Fin 16) :
    StripAssembly.StripChecked (StripAssembly.indexBlock02 k) := by
  fin_cases k
  · exact strip358_checked
  · exact strip359_checked
  · exact strip360_checked
  · exact strip361_checked
  · exact strip362_checked
  · exact strip363_checked
  · exact strip364_checked
  · exact strip365_checked
  · exact strip366_checked
  · exact strip367_checked
  · exact strip368_checked
  · exact strip369_checked
  · exact strip370_checked
  · exact strip371_checked
  · exact strip372_checked
  · exact strip373_checked

end ImbalancedChen.Certificates.PairedV2.FullMask
