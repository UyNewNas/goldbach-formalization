import ImbalancedChen.Certificates.PairedV2StripFiniteAssembly
import ImbalancedChen.Certificates.PairedV2StripCertificate497Left
import ImbalancedChen.Certificates.PairedV2StripCertificate497Right

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip497_checked : ∀ j : Fin (512 - firstU (⟨171, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨171, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨171, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  exact StripAssembly.forallFinCastAdd (a := 88) (b := 88)
    strip497_row_count
    (fun j => (makeCertificate (⟨(⟨171, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨171, by decide⟩ : Fin 186), j⟩ : Row))).check = true)
    strip497_checked_left strip497_checked_right

end ImbalancedChen.Certificates.PairedV2.FullMask
