import ImbalancedChen.Certificates.PairedV2StripFiniteAssembly
import ImbalancedChen.Certificates.PairedV2StripCertificate481Left
import ImbalancedChen.Certificates.PairedV2StripCertificate481Right

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip481_checked : ∀ j : Fin (512 - firstU (⟨155, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨155, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨155, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  exact StripAssembly.forallFinCastAdd (a := 79) (b := 80)
    strip481_row_count
    (fun j => (makeCertificate (⟨(⟨155, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨155, by decide⟩ : Fin 186), j⟩ : Row))).check = true)
    strip481_checked_left strip481_checked_right

end ImbalancedChen.Certificates.PairedV2.FullMask
