import ImbalancedChen.Certificates.PairedV2StripFiniteAssembly
import ImbalancedChen.Certificates.PairedV2StripCertificate458Left
import ImbalancedChen.Certificates.PairedV2StripCertificate458Right

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip458_checked : ∀ j : Fin (512 - firstU (⟨132, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨132, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨132, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  exact StripAssembly.forallFinCastAdd (a := 67) (b := 68)
    strip458_row_count
    (fun j => (makeCertificate (⟨(⟨132, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨132, by decide⟩ : Fin 186), j⟩ : Row))).check = true)
    strip458_checked_left strip458_checked_right

end ImbalancedChen.Certificates.PairedV2.FullMask
