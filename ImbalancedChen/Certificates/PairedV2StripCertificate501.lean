import ImbalancedChen.Certificates.PairedV2StripFiniteAssembly
import ImbalancedChen.Certificates.PairedV2StripCertificate501Left
import ImbalancedChen.Certificates.PairedV2StripCertificate501Right

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip501_checked : ∀ j : Fin (512 - firstU (⟨175, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨175, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨175, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  exact StripAssembly.forallFinCastAdd (a := 90) (b := 90)
    strip501_row_count
    (fun j => (makeCertificate (⟨(⟨175, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨175, by decide⟩ : Fin 186), j⟩ : Row))).check = true)
    strip501_checked_left strip501_checked_right

end ImbalancedChen.Certificates.PairedV2.FullMask
