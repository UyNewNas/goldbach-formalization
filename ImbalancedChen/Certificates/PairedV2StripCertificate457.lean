import ImbalancedChen.Certificates.PairedV2StripFiniteAssembly
import ImbalancedChen.Certificates.PairedV2StripCertificate457Left
import ImbalancedChen.Certificates.PairedV2StripCertificate457Right

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip457_checked : ∀ j : Fin (512 - firstU (⟨131, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨131, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨131, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  exact StripAssembly.forallFinCastAdd (a := 67) (b := 67)
    strip457_row_count
    (fun j => (makeCertificate (⟨(⟨131, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨131, by decide⟩ : Fin 186), j⟩ : Row))).check = true)
    strip457_checked_left strip457_checked_right

end ImbalancedChen.Certificates.PairedV2.FullMask
