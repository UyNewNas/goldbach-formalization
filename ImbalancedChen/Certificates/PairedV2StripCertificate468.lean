import ImbalancedChen.Certificates.PairedV2StripFiniteAssembly
import ImbalancedChen.Certificates.PairedV2StripCertificate468Left
import ImbalancedChen.Certificates.PairedV2StripCertificate468Right

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip468_checked : ∀ j : Fin (512 - firstU (⟨142, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨142, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨142, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  exact StripAssembly.forallFinCastAdd (a := 72) (b := 73)
    strip468_row_count
    (fun j => (makeCertificate (⟨(⟨142, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨142, by decide⟩ : Fin 186), j⟩ : Row))).check = true)
    strip468_checked_left strip468_checked_right

end ImbalancedChen.Certificates.PairedV2.FullMask
