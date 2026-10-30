import ImbalancedChen.Certificates.PairedV2StripFiniteAssembly
import ImbalancedChen.Certificates.PairedV2StripCertificate477Left
import ImbalancedChen.Certificates.PairedV2StripCertificate477Right

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip477_checked : ∀ j : Fin (512 - firstU (⟨151, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨151, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨151, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  exact StripAssembly.forallFinCastAdd (a := 77) (b := 78)
    strip477_row_count
    (fun j => (makeCertificate (⟨(⟨151, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨151, by decide⟩ : Fin 186), j⟩ : Row))).check = true)
    strip477_checked_left strip477_checked_right

end ImbalancedChen.Certificates.PairedV2.FullMask
