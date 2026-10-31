import ImbalancedChen.Certificates.PairedV2StripFiniteAssembly
import ImbalancedChen.Certificates.PairedV2StripCertificate508Left
import ImbalancedChen.Certificates.PairedV2StripCertificate508Right

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip508_checked : ∀ j : Fin (512 - firstU (⟨182, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨182, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨182, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  exact StripAssembly.forallFinCastAdd (a := 94) (b := 94)
    strip508_row_count
    (fun j => (makeCertificate (⟨(⟨182, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨182, by decide⟩ : Fin 186), j⟩ : Row))).check = true)
    strip508_checked_left strip508_checked_right

end ImbalancedChen.Certificates.PairedV2.FullMask
