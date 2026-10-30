import ImbalancedChen.Certificates.PairedV2StripFiniteAssembly
import ImbalancedChen.Certificates.PairedV2StripCertificate454Left
import ImbalancedChen.Certificates.PairedV2StripCertificate454Right

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip454_checked : ∀ j : Fin (512 - firstU (⟨128, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨128, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨128, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  exact StripAssembly.forallFinCastAdd (a := 65) (b := 66)
    strip454_row_count
    (fun j => (makeCertificate (⟨(⟨128, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨128, by decide⟩ : Fin 186), j⟩ : Row))).check = true)
    strip454_checked_left strip454_checked_right

end ImbalancedChen.Certificates.PairedV2.FullMask
