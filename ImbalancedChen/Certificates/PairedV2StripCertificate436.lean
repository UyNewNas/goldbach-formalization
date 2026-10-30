import ImbalancedChen.Certificates.PairedV2StripFiniteAssembly
import ImbalancedChen.Certificates.PairedV2StripCertificate436Left
import ImbalancedChen.Certificates.PairedV2StripCertificate436Right

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip436_checked : ∀ j : Fin (512 - firstU (⟨110, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨110, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨110, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  exact StripAssembly.forallFinCastAdd (a := 56) (b := 56)
    strip436_row_count
    (fun j => (makeCertificate (⟨(⟨110, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨110, by decide⟩ : Fin 186), j⟩ : Row))).check = true)
    strip436_checked_left strip436_checked_right

end ImbalancedChen.Certificates.PairedV2.FullMask
