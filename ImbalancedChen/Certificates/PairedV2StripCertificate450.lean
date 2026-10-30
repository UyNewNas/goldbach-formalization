import ImbalancedChen.Certificates.PairedV2StripFiniteAssembly
import ImbalancedChen.Certificates.PairedV2StripCertificate450Left
import ImbalancedChen.Certificates.PairedV2StripCertificate450Right

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip450_checked : ∀ j : Fin (512 - firstU (⟨124, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨124, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨124, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  exact StripAssembly.forallFinCastAdd (a := 63) (b := 63)
    strip450_row_count
    (fun j => (makeCertificate (⟨(⟨124, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨124, by decide⟩ : Fin 186), j⟩ : Row))).check = true)
    strip450_checked_left strip450_checked_right

end ImbalancedChen.Certificates.PairedV2.FullMask
