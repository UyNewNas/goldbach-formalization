import ImbalancedChen.Certificates.PairedV2StripFiniteAssembly
import ImbalancedChen.Certificates.PairedV2StripCertificate433Left
import ImbalancedChen.Certificates.PairedV2StripCertificate433Right

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip433_checked : ∀ j : Fin (512 - firstU (⟨107, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨107, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨107, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  exact StripAssembly.forallFinCastAdd (a := 54) (b := 55)
    strip433_row_count
    (fun j => (makeCertificate (⟨(⟨107, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨107, by decide⟩ : Fin 186), j⟩ : Row))).check = true)
    strip433_checked_left strip433_checked_right

end ImbalancedChen.Certificates.PairedV2.FullMask
