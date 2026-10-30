import ImbalancedChen.Certificates.PairedV2StripFiniteAssembly
import ImbalancedChen.Certificates.PairedV2StripCertificate485Left
import ImbalancedChen.Certificates.PairedV2StripCertificate485Right

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip485_checked : ∀ j : Fin (512 - firstU (⟨159, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨159, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨159, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  exact StripAssembly.forallFinCastAdd (a := 81) (b := 82)
    strip485_row_count
    (fun j => (makeCertificate (⟨(⟨159, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨159, by decide⟩ : Fin 186), j⟩ : Row))).check = true)
    strip485_checked_left strip485_checked_right

end ImbalancedChen.Certificates.PairedV2.FullMask
