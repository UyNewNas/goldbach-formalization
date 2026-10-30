import ImbalancedChen.Certificates.PairedV2StripFiniteAssembly
import ImbalancedChen.Certificates.PairedV2StripCertificate424Left
import ImbalancedChen.Certificates.PairedV2StripCertificate424Right

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip424_checked : ∀ j : Fin (512 - firstU (⟨98, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨98, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨98, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  exact StripAssembly.forallFinCastAdd (a := 50) (b := 50)
    strip424_row_count
    (fun j => (makeCertificate (⟨(⟨98, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨98, by decide⟩ : Fin 186), j⟩ : Row))).check = true)
    strip424_checked_left strip424_checked_right

end ImbalancedChen.Certificates.PairedV2.FullMask
