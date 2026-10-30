import ImbalancedChen.Certificates.PairedV2StripFiniteAssembly
import ImbalancedChen.Certificates.PairedV2StripCertificate435Left
import ImbalancedChen.Certificates.PairedV2StripCertificate435Right

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip435_checked : ∀ j : Fin (512 - firstU (⟨109, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨109, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨109, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  exact StripAssembly.forallFinCastAdd (a := 55) (b := 56)
    strip435_row_count
    (fun j => (makeCertificate (⟨(⟨109, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨109, by decide⟩ : Fin 186), j⟩ : Row))).check = true)
    strip435_checked_left strip435_checked_right

end ImbalancedChen.Certificates.PairedV2.FullMask
