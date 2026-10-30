import ImbalancedChen.Certificates.PairedV2StripFiniteAssembly
import ImbalancedChen.Certificates.PairedV2StripCertificate490Left
import ImbalancedChen.Certificates.PairedV2StripCertificate490Right

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip490_checked : ∀ j : Fin (512 - firstU (⟨164, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨164, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨164, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  exact StripAssembly.forallFinCastAdd (a := 84) (b := 85)
    strip490_row_count
    (fun j => (makeCertificate (⟨(⟨164, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨164, by decide⟩ : Fin 186), j⟩ : Row))).check = true)
    strip490_checked_left strip490_checked_right

end ImbalancedChen.Certificates.PairedV2.FullMask
