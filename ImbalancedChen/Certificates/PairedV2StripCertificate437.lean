import ImbalancedChen.Certificates.PairedV2StripFiniteAssembly
import ImbalancedChen.Certificates.PairedV2StripCertificate437Left
import ImbalancedChen.Certificates.PairedV2StripCertificate437Right

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip437_checked : ∀ j : Fin (512 - firstU (⟨111, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨111, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨111, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  exact StripAssembly.forallFinCastAdd (a := 56) (b := 57)
    strip437_row_count
    (fun j => (makeCertificate (⟨(⟨111, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨111, by decide⟩ : Fin 186), j⟩ : Row))).check = true)
    strip437_checked_left strip437_checked_right

end ImbalancedChen.Certificates.PairedV2.FullMask
