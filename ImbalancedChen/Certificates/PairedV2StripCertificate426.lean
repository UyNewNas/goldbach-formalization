import ImbalancedChen.Certificates.PairedV2StripFiniteAssembly
import ImbalancedChen.Certificates.PairedV2StripCertificate426Left
import ImbalancedChen.Certificates.PairedV2StripCertificate426Right

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip426_checked : ∀ j : Fin (512 - firstU (⟨100, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨100, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨100, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  exact StripAssembly.forallFinCastAdd (a := 51) (b := 51)
    strip426_row_count
    (fun j => (makeCertificate (⟨(⟨100, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨100, by decide⟩ : Fin 186), j⟩ : Row))).check = true)
    strip426_checked_left strip426_checked_right

end ImbalancedChen.Certificates.PairedV2.FullMask
