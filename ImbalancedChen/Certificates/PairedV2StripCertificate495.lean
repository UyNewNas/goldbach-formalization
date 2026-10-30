import ImbalancedChen.Certificates.PairedV2StripFiniteAssembly
import ImbalancedChen.Certificates.PairedV2StripCertificate495Left
import ImbalancedChen.Certificates.PairedV2StripCertificate495Right

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip495_checked : ∀ j : Fin (512 - firstU (⟨169, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨169, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨169, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  exact StripAssembly.forallFinCastAdd (a := 87) (b := 87)
    strip495_row_count
    (fun j => (makeCertificate (⟨(⟨169, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨169, by decide⟩ : Fin 186), j⟩ : Row))).check = true)
    strip495_checked_left strip495_checked_right

end ImbalancedChen.Certificates.PairedV2.FullMask
