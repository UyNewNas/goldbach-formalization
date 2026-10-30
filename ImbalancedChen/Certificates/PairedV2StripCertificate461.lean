import ImbalancedChen.Certificates.PairedV2StripFiniteAssembly
import ImbalancedChen.Certificates.PairedV2StripCertificate461Left
import ImbalancedChen.Certificates.PairedV2StripCertificate461Right

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip461_checked : ∀ j : Fin (512 - firstU (⟨135, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨135, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨135, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  exact StripAssembly.forallFinCastAdd (a := 69) (b := 69)
    strip461_row_count
    (fun j => (makeCertificate (⟨(⟨135, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨135, by decide⟩ : Fin 186), j⟩ : Row))).check = true)
    strip461_checked_left strip461_checked_right

end ImbalancedChen.Certificates.PairedV2.FullMask
