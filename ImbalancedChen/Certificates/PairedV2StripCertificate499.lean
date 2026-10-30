import ImbalancedChen.Certificates.PairedV2StripFiniteAssembly
import ImbalancedChen.Certificates.PairedV2StripCertificate499Left
import ImbalancedChen.Certificates.PairedV2StripCertificate499Right

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip499_checked : ∀ j : Fin (512 - firstU (⟨173, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨173, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨173, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  exact StripAssembly.forallFinCastAdd (a := 89) (b := 89)
    strip499_row_count
    (fun j => (makeCertificate (⟨(⟨173, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨173, by decide⟩ : Fin 186), j⟩ : Row))).check = true)
    strip499_checked_left strip499_checked_right

end ImbalancedChen.Certificates.PairedV2.FullMask
