import ImbalancedChen.Certificates.PairedV2StripFiniteAssembly
import ImbalancedChen.Certificates.PairedV2StripCertificate486Left
import ImbalancedChen.Certificates.PairedV2StripCertificate486Right

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip486_checked : ∀ j : Fin (512 - firstU (⟨160, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨160, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨160, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  exact StripAssembly.forallFinCastAdd (a := 82) (b := 82)
    strip486_row_count
    (fun j => (makeCertificate (⟨(⟨160, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨160, by decide⟩ : Fin 186), j⟩ : Row))).check = true)
    strip486_checked_left strip486_checked_right

end ImbalancedChen.Certificates.PairedV2.FullMask
