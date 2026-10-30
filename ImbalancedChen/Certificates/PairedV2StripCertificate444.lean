import ImbalancedChen.Certificates.PairedV2StripFiniteAssembly
import ImbalancedChen.Certificates.PairedV2StripCertificate444Left
import ImbalancedChen.Certificates.PairedV2StripCertificate444Right

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip444_checked : ∀ j : Fin (512 - firstU (⟨118, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨118, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨118, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  exact StripAssembly.forallFinCastAdd (a := 60) (b := 60)
    strip444_row_count
    (fun j => (makeCertificate (⟨(⟨118, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨118, by decide⟩ : Fin 186), j⟩ : Row))).check = true)
    strip444_checked_left strip444_checked_right

end ImbalancedChen.Certificates.PairedV2.FullMask
