import ImbalancedChen.Certificates.PairedV2StripFiniteAssembly
import ImbalancedChen.Certificates.PairedV2StripCertificate506Left
import ImbalancedChen.Certificates.PairedV2StripCertificate506Right

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip506_checked : ∀ j : Fin (512 - firstU (⟨180, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨180, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨180, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  exact StripAssembly.forallFinCastAdd (a := 92) (b := 93)
    strip506_row_count
    (fun j => (makeCertificate (⟨(⟨180, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨180, by decide⟩ : Fin 186), j⟩ : Row))).check = true)
    strip506_checked_left strip506_checked_right

end ImbalancedChen.Certificates.PairedV2.FullMask
