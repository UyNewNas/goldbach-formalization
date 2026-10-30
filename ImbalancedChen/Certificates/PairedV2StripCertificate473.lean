import ImbalancedChen.Certificates.PairedV2StripFiniteAssembly
import ImbalancedChen.Certificates.PairedV2StripCertificate473Left
import ImbalancedChen.Certificates.PairedV2StripCertificate473Right

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip473_checked : ∀ j : Fin (512 - firstU (⟨147, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨147, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨147, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  exact StripAssembly.forallFinCastAdd (a := 75) (b := 75)
    strip473_row_count
    (fun j => (makeCertificate (⟨(⟨147, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨147, by decide⟩ : Fin 186), j⟩ : Row))).check = true)
    strip473_checked_left strip473_checked_right

end ImbalancedChen.Certificates.PairedV2.FullMask
