import ImbalancedChen.Certificates.PairedV2StripFiniteAssembly
import ImbalancedChen.Certificates.PairedV2StripCertificate423Left
import ImbalancedChen.Certificates.PairedV2StripCertificate423Right

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip423_checked : ∀ j : Fin (512 - firstU (⟨97, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨97, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨97, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  exact StripAssembly.forallFinCastAdd (a := 49) (b := 49)
    strip423_row_count
    (fun j => (makeCertificate (⟨(⟨97, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨97, by decide⟩ : Fin 186), j⟩ : Row))).check = true)
    strip423_checked_left strip423_checked_right

end ImbalancedChen.Certificates.PairedV2.FullMask
