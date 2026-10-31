import ImbalancedChen.Certificates.PairedV2StripFiniteAssembly
import ImbalancedChen.Certificates.PairedV2StripCertificate510Left
import ImbalancedChen.Certificates.PairedV2StripCertificate510Right

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip510_checked : ∀ j : Fin (512 - firstU (⟨184, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨184, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨184, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  exact StripAssembly.forallFinCastAdd (a := 95) (b := 95)
    strip510_row_count
    (fun j => (makeCertificate (⟨(⟨184, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨184, by decide⟩ : Fin 186), j⟩ : Row))).check = true)
    strip510_checked_left strip510_checked_right

end ImbalancedChen.Certificates.PairedV2.FullMask
