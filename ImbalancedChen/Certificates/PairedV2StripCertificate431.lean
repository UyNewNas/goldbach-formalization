import ImbalancedChen.Certificates.PairedV2StripFiniteAssembly
import ImbalancedChen.Certificates.PairedV2StripCertificate431Left
import ImbalancedChen.Certificates.PairedV2StripCertificate431Right

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip431_checked : ∀ j : Fin (512 - firstU (⟨105, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨105, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨105, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  exact StripAssembly.forallFinCastAdd (a := 53) (b := 54)
    strip431_row_count
    (fun j => (makeCertificate (⟨(⟨105, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨105, by decide⟩ : Fin 186), j⟩ : Row))).check = true)
    strip431_checked_left strip431_checked_right

end ImbalancedChen.Certificates.PairedV2.FullMask
