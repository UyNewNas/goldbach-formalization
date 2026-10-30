import ImbalancedChen.Certificates.PairedV2StripFiniteAssembly
import ImbalancedChen.Certificates.PairedV2StripCertificate494Left
import ImbalancedChen.Certificates.PairedV2StripCertificate494Right

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip494_checked : ∀ j : Fin (512 - firstU (⟨168, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨168, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨168, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  exact StripAssembly.forallFinCastAdd (a := 86) (b := 87)
    strip494_row_count
    (fun j => (makeCertificate (⟨(⟨168, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨168, by decide⟩ : Fin 186), j⟩ : Row))).check = true)
    strip494_checked_left strip494_checked_right

end ImbalancedChen.Certificates.PairedV2.FullMask
