import ImbalancedChen.Certificates.PairedV2StripCertificate342
import ImbalancedChen.Certificates.PairedV2StripCertificate343
import ImbalancedChen.Certificates.PairedV2StripCertificate344
import ImbalancedChen.Certificates.PairedV2StripCertificate345
import ImbalancedChen.Certificates.PairedV2StripCertificate346
import ImbalancedChen.Certificates.PairedV2StripCertificate347
import ImbalancedChen.Certificates.PairedV2StripCertificate348
import ImbalancedChen.Certificates.PairedV2StripCertificate349
import ImbalancedChen.Certificates.PairedV2StripCertificate350
import ImbalancedChen.Certificates.PairedV2StripCertificate351
import ImbalancedChen.Certificates.PairedV2StripCertificate352
import ImbalancedChen.Certificates.PairedV2StripCertificate353
import ImbalancedChen.Certificates.PairedV2StripCertificate354
import ImbalancedChen.Certificates.PairedV2StripCertificate355
import ImbalancedChen.Certificates.PairedV2StripCertificate356
import ImbalancedChen.Certificates.PairedV2StripCertificate357

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Bounded composition of the original strip checks, with no new check assumption. -/
theorem stripBlock01_checked (k : Fin 16) :
    StripAssembly.StripChecked (StripAssembly.indexBlock01 k) := by
  fin_cases k
  · exact strip342_checked
  · exact strip343_checked
  · exact strip344_checked
  · exact strip345_checked
  · exact strip346_checked
  · exact strip347_checked
  · exact strip348_checked
  · exact strip349_checked
  · exact strip350_checked
  · exact strip351_checked
  · exact strip352_checked
  · exact strip353_checked
  · exact strip354_checked
  · exact strip355_checked
  · exact strip356_checked
  · exact strip357_checked

end ImbalancedChen.Certificates.PairedV2.FullMask
