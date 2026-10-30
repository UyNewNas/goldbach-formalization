import ImbalancedChen.Certificates.PairedV2StripCertificate486
import ImbalancedChen.Certificates.PairedV2StripCertificate487
import ImbalancedChen.Certificates.PairedV2StripCertificate488
import ImbalancedChen.Certificates.PairedV2StripCertificate489
import ImbalancedChen.Certificates.PairedV2StripCertificate490
import ImbalancedChen.Certificates.PairedV2StripCertificate491
import ImbalancedChen.Certificates.PairedV2StripCertificate492
import ImbalancedChen.Certificates.PairedV2StripCertificate493
import ImbalancedChen.Certificates.PairedV2StripCertificate494
import ImbalancedChen.Certificates.PairedV2StripCertificate495
import ImbalancedChen.Certificates.PairedV2StripCertificate496
import ImbalancedChen.Certificates.PairedV2StripCertificate497
import ImbalancedChen.Certificates.PairedV2StripCertificate498
import ImbalancedChen.Certificates.PairedV2StripCertificate499
import ImbalancedChen.Certificates.PairedV2StripCertificate500
import ImbalancedChen.Certificates.PairedV2StripCertificate501

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Bounded composition of the original strip checks, with no new check assumption. -/
theorem stripBlock10_checked (k : Fin 16) :
    StripAssembly.StripChecked (StripAssembly.indexBlock10 k) := by
  fin_cases k
  · exact strip486_checked
  · exact strip487_checked
  · exact strip488_checked
  · exact strip489_checked
  · exact strip490_checked
  · exact strip491_checked
  · exact strip492_checked
  · exact strip493_checked
  · exact strip494_checked
  · exact strip495_checked
  · exact strip496_checked
  · exact strip497_checked
  · exact strip498_checked
  · exact strip499_checked
  · exact strip500_checked
  · exact strip501_checked

end ImbalancedChen.Certificates.PairedV2.FullMask
