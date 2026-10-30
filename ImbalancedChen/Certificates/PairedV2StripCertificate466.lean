import ImbalancedChen.Certificates.PairedV2StripFiniteAssembly
import ImbalancedChen.Certificates.PairedV2StripCertificate466Left
import ImbalancedChen.Certificates.PairedV2StripCertificate466Right

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip466_checked : ∀ j : Fin (512 - firstU (⟨140, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨140, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨140, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  exact StripAssembly.forallFinCastAdd (a := 71) (b := 72)
    strip466_row_count
    (fun j => (makeCertificate (⟨(⟨140, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨140, by decide⟩ : Fin 186), j⟩ : Row))).check = true)
    strip466_checked_left strip466_checked_right

end ImbalancedChen.Certificates.PairedV2.FullMask
