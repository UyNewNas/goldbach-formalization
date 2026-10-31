import ImbalancedChen.Certificates.PairedV2StripFiniteAssembly
import ImbalancedChen.Certificates.PairedV2StripCertificate507Left
import ImbalancedChen.Certificates.PairedV2StripCertificate507Right

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip507_checked : ∀ j : Fin (512 - firstU (⟨181, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨181, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨181, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  exact StripAssembly.forallFinCastAdd (a := 93) (b := 94)
    strip507_row_count
    (fun j => (makeCertificate (⟨(⟨181, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨181, by decide⟩ : Fin 186), j⟩ : Row))).check = true)
    strip507_checked_left strip507_checked_right

end ImbalancedChen.Certificates.PairedV2.FullMask
