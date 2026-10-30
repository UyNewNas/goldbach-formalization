import ImbalancedChen.Certificates.PairedV2StripFiniteAssembly
import ImbalancedChen.Certificates.PairedV2StripCertificate483Left
import ImbalancedChen.Certificates.PairedV2StripCertificate483Right

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip483_checked : ∀ j : Fin (512 - firstU (⟨157, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨157, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨157, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  exact StripAssembly.forallFinCastAdd (a := 80) (b := 81)
    strip483_row_count
    (fun j => (makeCertificate (⟨(⟨157, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨157, by decide⟩ : Fin 186), j⟩ : Row))).check = true)
    strip483_checked_left strip483_checked_right

end ImbalancedChen.Certificates.PairedV2.FullMask
