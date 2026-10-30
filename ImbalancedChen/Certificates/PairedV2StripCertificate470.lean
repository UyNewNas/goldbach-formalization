import ImbalancedChen.Certificates.PairedV2StripFiniteAssembly
import ImbalancedChen.Certificates.PairedV2StripCertificate470Left
import ImbalancedChen.Certificates.PairedV2StripCertificate470Right

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip470_checked : ∀ j : Fin (512 - firstU (⟨144, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨144, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨144, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  exact StripAssembly.forallFinCastAdd (a := 73) (b := 74)
    strip470_row_count
    (fun j => (makeCertificate (⟨(⟨144, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨144, by decide⟩ : Fin 186), j⟩ : Row))).check = true)
    strip470_checked_left strip470_checked_right

end ImbalancedChen.Certificates.PairedV2.FullMask
