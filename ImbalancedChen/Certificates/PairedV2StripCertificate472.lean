import ImbalancedChen.Certificates.PairedV2StripFiniteAssembly
import ImbalancedChen.Certificates.PairedV2StripCertificate472Left
import ImbalancedChen.Certificates.PairedV2StripCertificate472Right

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip472_checked : ∀ j : Fin (512 - firstU (⟨146, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨146, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨146, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  exact StripAssembly.forallFinCastAdd (a := 74) (b := 75)
    strip472_row_count
    (fun j => (makeCertificate (⟨(⟨146, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨146, by decide⟩ : Fin 186), j⟩ : Row))).check = true)
    strip472_checked_left strip472_checked_right

end ImbalancedChen.Certificates.PairedV2.FullMask
