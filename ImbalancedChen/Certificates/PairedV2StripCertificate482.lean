import ImbalancedChen.Certificates.PairedV2StripFiniteAssembly
import ImbalancedChen.Certificates.PairedV2StripCertificate482Left
import ImbalancedChen.Certificates.PairedV2StripCertificate482Right

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip482_checked : ∀ j : Fin (512 - firstU (⟨156, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨156, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨156, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  exact StripAssembly.forallFinCastAdd (a := 80) (b := 80)
    strip482_row_count
    (fun j => (makeCertificate (⟨(⟨156, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨156, by decide⟩ : Fin 186), j⟩ : Row))).check = true)
    strip482_checked_left strip482_checked_right

end ImbalancedChen.Certificates.PairedV2.FullMask
