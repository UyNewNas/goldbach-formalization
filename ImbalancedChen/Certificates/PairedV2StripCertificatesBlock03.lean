import ImbalancedChen.Certificates.PairedV2StripCertificate374
import ImbalancedChen.Certificates.PairedV2StripCertificate375
import ImbalancedChen.Certificates.PairedV2StripCertificate376
import ImbalancedChen.Certificates.PairedV2StripCertificate377
import ImbalancedChen.Certificates.PairedV2StripCertificate378
import ImbalancedChen.Certificates.PairedV2StripCertificate379
import ImbalancedChen.Certificates.PairedV2StripCertificate380
import ImbalancedChen.Certificates.PairedV2StripCertificate381
import ImbalancedChen.Certificates.PairedV2StripCertificate382
import ImbalancedChen.Certificates.PairedV2StripCertificate383
import ImbalancedChen.Certificates.PairedV2StripCertificate384
import ImbalancedChen.Certificates.PairedV2StripCertificate385
import ImbalancedChen.Certificates.PairedV2StripCertificate386
import ImbalancedChen.Certificates.PairedV2StripCertificate387
import ImbalancedChen.Certificates.PairedV2StripCertificate388
import ImbalancedChen.Certificates.PairedV2StripCertificate389

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Bounded composition of the original strip checks, with no new check assumption. -/
theorem stripBlock03_checked (k : Fin 16) :
    StripAssembly.StripChecked (StripAssembly.indexBlock03 k) := by
  fin_cases k
  · exact strip374_checked
  · exact strip375_checked
  · exact strip376_checked
  · exact strip377_checked
  · exact strip378_checked
  · exact strip379_checked
  · exact strip380_checked
  · exact strip381_checked
  · exact strip382_checked
  · exact strip383_checked
  · exact strip384_checked
  · exact strip385_checked
  · exact strip386_checked
  · exact strip387_checked
  · exact strip388_checked
  · exact strip389_checked

end ImbalancedChen.Certificates.PairedV2.FullMask
