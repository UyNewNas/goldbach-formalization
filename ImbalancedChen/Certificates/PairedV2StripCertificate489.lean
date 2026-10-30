import ImbalancedChen.Certificates.PairedV2StripFiniteAssembly
import ImbalancedChen.Certificates.PairedV2StripCertificate489Left
import ImbalancedChen.Certificates.PairedV2StripCertificate489Right

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip489_checked : ∀ j : Fin (512 - firstU (⟨163, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨163, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨163, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  exact StripAssembly.forallFinCastAdd (a := 84) (b := 84)
    strip489_row_count
    (fun j => (makeCertificate (⟨(⟨163, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨163, by decide⟩ : Fin 186), j⟩ : Row))).check = true)
    strip489_checked_left strip489_checked_right

end ImbalancedChen.Certificates.PairedV2.FullMask
