import ImbalancedChen.Certificates.PairedV2StripFiniteAssembly
import ImbalancedChen.Certificates.PairedV2StripCertificate413Left
import ImbalancedChen.Certificates.PairedV2StripCertificate413Right

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip413_checked : ∀ j : Fin (512 - firstU (⟨87, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨87, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨87, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  exact StripAssembly.forallFinCastAdd (a := 44) (b := 44)
    strip413_row_count
    (fun j => (makeCertificate (⟨(⟨87, by decide⟩ : Fin 186), j⟩ : Row)
      (approximation (⟨(⟨87, by decide⟩ : Fin 186), j⟩ : Row))).check = true)
    strip413_checked_left strip413_checked_right

end ImbalancedChen.Certificates.PairedV2.FullMask
