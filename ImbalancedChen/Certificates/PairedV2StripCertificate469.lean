import ImbalancedChen.Certificates.PairedV2StripFiniteAssembly
import ImbalancedChen.Certificates.PairedV2StripCertificate469Left
import ImbalancedChen.Certificates.PairedV2StripCertificate469Right

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip469_checked : ∀ j : Fin (512 - firstU (⟨143, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨143, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨143, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  exact StripAssembly.forallFinCastAdd (a := 73) (b := 74)
    strip469_row_count
    (fun j => (makeCertificate (⟨(⟨143, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨143, by decide⟩ : Fin 186), j⟩ : Row))).check = true)
    strip469_checked_left strip469_checked_right

end ImbalancedChen.Certificates.PairedV2.FullMask
