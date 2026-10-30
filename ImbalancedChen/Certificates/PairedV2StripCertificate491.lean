import ImbalancedChen.Certificates.PairedV2StripFiniteAssembly
import ImbalancedChen.Certificates.PairedV2StripCertificate491Left
import ImbalancedChen.Certificates.PairedV2StripCertificate491Right

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip491_checked : ∀ j : Fin (512 - firstU (⟨165, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨165, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨165, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  exact StripAssembly.forallFinCastAdd (a := 85) (b := 85)
    strip491_row_count
    (fun j => (makeCertificate (⟨(⟨165, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨165, by decide⟩ : Fin 186), j⟩ : Row))).check = true)
    strip491_checked_left strip491_checked_right

end ImbalancedChen.Certificates.PairedV2.FullMask
