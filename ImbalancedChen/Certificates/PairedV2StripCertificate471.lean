import ImbalancedChen.Certificates.PairedV2StripFiniteAssembly
import ImbalancedChen.Certificates.PairedV2StripCertificate471Left
import ImbalancedChen.Certificates.PairedV2StripCertificate471Right

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip471_checked : ∀ j : Fin (512 - firstU (⟨145, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨145, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨145, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  exact StripAssembly.forallFinCastAdd (a := 74) (b := 74)
    strip471_row_count
    (fun j => (makeCertificate (⟨(⟨145, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨145, by decide⟩ : Fin 186), j⟩ : Row))).check = true)
    strip471_checked_left strip471_checked_right

end ImbalancedChen.Certificates.PairedV2.FullMask
