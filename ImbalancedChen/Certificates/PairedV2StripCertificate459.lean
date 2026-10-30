import ImbalancedChen.Certificates.PairedV2StripFiniteAssembly
import ImbalancedChen.Certificates.PairedV2StripCertificate459Left
import ImbalancedChen.Certificates.PairedV2StripCertificate459Right

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip459_checked : ∀ j : Fin (512 - firstU (⟨133, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨133, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨133, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  exact StripAssembly.forallFinCastAdd (a := 68) (b := 68)
    strip459_row_count
    (fun j => (makeCertificate (⟨(⟨133, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨133, by decide⟩ : Fin 186), j⟩ : Row))).check = true)
    strip459_checked_left strip459_checked_right

end ImbalancedChen.Certificates.PairedV2.FullMask
