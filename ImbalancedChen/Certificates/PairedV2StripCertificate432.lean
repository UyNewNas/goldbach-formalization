import ImbalancedChen.Certificates.PairedV2StripFiniteAssembly
import ImbalancedChen.Certificates.PairedV2StripCertificate432Left
import ImbalancedChen.Certificates.PairedV2StripCertificate432Right

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip432_checked : ∀ j : Fin (512 - firstU (⟨106, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨106, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨106, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  exact StripAssembly.forallFinCastAdd (a := 54) (b := 54)
    strip432_row_count
    (fun j => (makeCertificate (⟨(⟨106, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨106, by decide⟩ : Fin 186), j⟩ : Row))).check = true)
    strip432_checked_left strip432_checked_right

end ImbalancedChen.Certificates.PairedV2.FullMask
