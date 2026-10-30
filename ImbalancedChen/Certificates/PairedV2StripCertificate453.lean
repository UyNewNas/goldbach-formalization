import ImbalancedChen.Certificates.PairedV2StripFiniteAssembly
import ImbalancedChen.Certificates.PairedV2StripCertificate453Left
import ImbalancedChen.Certificates.PairedV2StripCertificate453Right

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip453_checked : ∀ j : Fin (512 - firstU (⟨127, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨127, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨127, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  exact StripAssembly.forallFinCastAdd (a := 65) (b := 65)
    strip453_row_count
    (fun j => (makeCertificate (⟨(⟨127, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨127, by decide⟩ : Fin 186), j⟩ : Row))).check = true)
    strip453_checked_left strip453_checked_right

end ImbalancedChen.Certificates.PairedV2.FullMask
