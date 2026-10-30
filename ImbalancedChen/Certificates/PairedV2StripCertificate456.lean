import ImbalancedChen.Certificates.PairedV2StripFiniteAssembly
import ImbalancedChen.Certificates.PairedV2StripCertificate456Left
import ImbalancedChen.Certificates.PairedV2StripCertificate456Right

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip456_checked : ∀ j : Fin (512 - firstU (⟨130, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨130, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨130, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  exact StripAssembly.forallFinCastAdd (a := 66) (b := 67)
    strip456_row_count
    (fun j => (makeCertificate (⟨(⟨130, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨130, by decide⟩ : Fin 186), j⟩ : Row))).check = true)
    strip456_checked_left strip456_checked_right

end ImbalancedChen.Certificates.PairedV2.FullMask
