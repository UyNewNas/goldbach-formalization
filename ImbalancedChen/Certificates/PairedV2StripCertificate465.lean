import ImbalancedChen.Certificates.PairedV2StripFiniteAssembly
import ImbalancedChen.Certificates.PairedV2StripCertificate465Left
import ImbalancedChen.Certificates.PairedV2StripCertificate465Right

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip465_checked : ∀ j : Fin (512 - firstU (⟨139, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨139, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨139, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  exact StripAssembly.forallFinCastAdd (a := 71) (b := 71)
    strip465_row_count
    (fun j => (makeCertificate (⟨(⟨139, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨139, by decide⟩ : Fin 186), j⟩ : Row))).check = true)
    strip465_checked_left strip465_checked_right

end ImbalancedChen.Certificates.PairedV2.FullMask
