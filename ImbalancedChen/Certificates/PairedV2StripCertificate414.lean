import ImbalancedChen.Certificates.PairedV2StripFiniteAssembly
import ImbalancedChen.Certificates.PairedV2StripCertificate414Left
import ImbalancedChen.Certificates.PairedV2StripCertificate414Right

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip414_checked : ∀ j : Fin (512 - firstU (⟨88, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨88, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨88, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  exact StripAssembly.forallFinCastAdd (a := 44) (b := 45)
    strip414_row_count
    (fun j => (makeCertificate (⟨(⟨88, by decide⟩ : Fin 186), j⟩ : Row)
      (approximation (⟨(⟨88, by decide⟩ : Fin 186), j⟩ : Row))).check = true)
    strip414_checked_left strip414_checked_right

end ImbalancedChen.Certificates.PairedV2.FullMask
