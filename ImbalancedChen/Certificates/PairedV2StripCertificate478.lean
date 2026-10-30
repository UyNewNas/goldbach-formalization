import ImbalancedChen.Certificates.PairedV2StripFiniteAssembly
import ImbalancedChen.Certificates.PairedV2StripCertificate478Left
import ImbalancedChen.Certificates.PairedV2StripCertificate478Right

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip478_checked : ∀ j : Fin (512 - firstU (⟨152, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨152, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨152, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  exact StripAssembly.forallFinCastAdd (a := 78) (b := 78)
    strip478_row_count
    (fun j => (makeCertificate (⟨(⟨152, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨152, by decide⟩ : Fin 186), j⟩ : Row))).check = true)
    strip478_checked_left strip478_checked_right

end ImbalancedChen.Certificates.PairedV2.FullMask
