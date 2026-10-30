import ImbalancedChen.Certificates.PairedV2StripFiniteAssembly
import ImbalancedChen.Certificates.PairedV2StripCertificate479Left
import ImbalancedChen.Certificates.PairedV2StripCertificate479Right

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip479_checked : ∀ j : Fin (512 - firstU (⟨153, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨153, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨153, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  exact StripAssembly.forallFinCastAdd (a := 78) (b := 79)
    strip479_row_count
    (fun j => (makeCertificate (⟨(⟨153, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨153, by decide⟩ : Fin 186), j⟩ : Row))).check = true)
    strip479_checked_left strip479_checked_right

end ImbalancedChen.Certificates.PairedV2.FullMask
