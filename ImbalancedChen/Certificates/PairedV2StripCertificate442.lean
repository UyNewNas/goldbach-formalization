import ImbalancedChen.Certificates.PairedV2StripFiniteAssembly
import ImbalancedChen.Certificates.PairedV2StripCertificate442Left
import ImbalancedChen.Certificates.PairedV2StripCertificate442Right

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip442_checked : ∀ j : Fin (512 - firstU (⟨116, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨116, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨116, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  exact StripAssembly.forallFinCastAdd (a := 59) (b := 59)
    strip442_row_count
    (fun j => (makeCertificate (⟨(⟨116, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨116, by decide⟩ : Fin 186), j⟩ : Row))).check = true)
    strip442_checked_left strip442_checked_right

end ImbalancedChen.Certificates.PairedV2.FullMask
