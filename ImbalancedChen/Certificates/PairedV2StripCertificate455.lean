import ImbalancedChen.Certificates.PairedV2StripFiniteAssembly
import ImbalancedChen.Certificates.PairedV2StripCertificate455Left
import ImbalancedChen.Certificates.PairedV2StripCertificate455Right

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip455_checked : ∀ j : Fin (512 - firstU (⟨129, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨129, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨129, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  exact StripAssembly.forallFinCastAdd (a := 66) (b := 66)
    strip455_row_count
    (fun j => (makeCertificate (⟨(⟨129, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨129, by decide⟩ : Fin 186), j⟩ : Row))).check = true)
    strip455_checked_left strip455_checked_right

end ImbalancedChen.Certificates.PairedV2.FullMask
