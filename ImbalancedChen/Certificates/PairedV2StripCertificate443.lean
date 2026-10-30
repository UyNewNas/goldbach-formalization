import ImbalancedChen.Certificates.PairedV2StripFiniteAssembly
import ImbalancedChen.Certificates.PairedV2StripCertificate443Left
import ImbalancedChen.Certificates.PairedV2StripCertificate443Right

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip443_checked : ∀ j : Fin (512 - firstU (⟨117, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨117, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨117, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  exact StripAssembly.forallFinCastAdd (a := 59) (b := 60)
    strip443_row_count
    (fun j => (makeCertificate (⟨(⟨117, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨117, by decide⟩ : Fin 186), j⟩ : Row))).check = true)
    strip443_checked_left strip443_checked_right

end ImbalancedChen.Certificates.PairedV2.FullMask
