import ImbalancedChen.Certificates.PairedV2StripFiniteAssembly
import ImbalancedChen.Certificates.PairedV2StripCertificate476Left
import ImbalancedChen.Certificates.PairedV2StripCertificate476Right

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip476_checked : ∀ j : Fin (512 - firstU (⟨150, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨150, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨150, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  exact StripAssembly.forallFinCastAdd (a := 77) (b := 77)
    strip476_row_count
    (fun j => (makeCertificate (⟨(⟨150, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨150, by decide⟩ : Fin 186), j⟩ : Row))).check = true)
    strip476_checked_left strip476_checked_right

end ImbalancedChen.Certificates.PairedV2.FullMask
