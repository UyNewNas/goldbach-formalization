import ImbalancedChen.Certificates.PairedV2StripFiniteAssembly
import ImbalancedChen.Certificates.PairedV2StripCertificate503Left
import ImbalancedChen.Certificates.PairedV2StripCertificate503Right

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip503_checked : ∀ j : Fin (512 - firstU (⟨177, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨177, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨177, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  exact StripAssembly.forallFinCastAdd (a := 91) (b := 91)
    strip503_row_count
    (fun j => (makeCertificate (⟨(⟨177, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨177, by decide⟩ : Fin 186), j⟩ : Row))).check = true)
    strip503_checked_left strip503_checked_right

end ImbalancedChen.Certificates.PairedV2.FullMask
