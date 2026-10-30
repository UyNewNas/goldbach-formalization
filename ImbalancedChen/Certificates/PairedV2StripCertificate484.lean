import ImbalancedChen.Certificates.PairedV2StripFiniteAssembly
import ImbalancedChen.Certificates.PairedV2StripCertificate484Left
import ImbalancedChen.Certificates.PairedV2StripCertificate484Right

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip484_checked : ∀ j : Fin (512 - firstU (⟨158, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨158, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨158, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  exact StripAssembly.forallFinCastAdd (a := 81) (b := 81)
    strip484_row_count
    (fun j => (makeCertificate (⟨(⟨158, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨158, by decide⟩ : Fin 186), j⟩ : Row))).check = true)
    strip484_checked_left strip484_checked_right

end ImbalancedChen.Certificates.PairedV2.FullMask
