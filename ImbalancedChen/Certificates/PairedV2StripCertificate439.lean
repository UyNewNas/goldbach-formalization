import ImbalancedChen.Certificates.PairedV2StripFiniteAssembly
import ImbalancedChen.Certificates.PairedV2StripCertificate439Left
import ImbalancedChen.Certificates.PairedV2StripCertificate439Right

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip439_checked : ∀ j : Fin (512 - firstU (⟨113, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨113, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨113, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  exact StripAssembly.forallFinCastAdd (a := 57) (b := 58)
    strip439_row_count
    (fun j => (makeCertificate (⟨(⟨113, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨113, by decide⟩ : Fin 186), j⟩ : Row))).check = true)
    strip439_checked_left strip439_checked_right

end ImbalancedChen.Certificates.PairedV2.FullMask
