import ImbalancedChen.Certificates.PairedV2StripFiniteAssembly
import ImbalancedChen.Certificates.PairedV2StripCertificate498Left
import ImbalancedChen.Certificates.PairedV2StripCertificate498Right

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip498_checked : ∀ j : Fin (512 - firstU (⟨172, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨172, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨172, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  exact StripAssembly.forallFinCastAdd (a := 88) (b := 89)
    strip498_row_count
    (fun j => (makeCertificate (⟨(⟨172, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨172, by decide⟩ : Fin 186), j⟩ : Row))).check = true)
    strip498_checked_left strip498_checked_right

end ImbalancedChen.Certificates.PairedV2.FullMask
