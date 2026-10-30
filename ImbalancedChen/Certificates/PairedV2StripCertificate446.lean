import ImbalancedChen.Certificates.PairedV2StripFiniteAssembly
import ImbalancedChen.Certificates.PairedV2StripCertificate446Left
import ImbalancedChen.Certificates.PairedV2StripCertificate446Right

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip446_checked : ∀ j : Fin (512 - firstU (⟨120, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨120, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨120, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  exact StripAssembly.forallFinCastAdd (a := 61) (b := 61)
    strip446_row_count
    (fun j => (makeCertificate (⟨(⟨120, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨120, by decide⟩ : Fin 186), j⟩ : Row))).check = true)
    strip446_checked_left strip446_checked_right

end ImbalancedChen.Certificates.PairedV2.FullMask
