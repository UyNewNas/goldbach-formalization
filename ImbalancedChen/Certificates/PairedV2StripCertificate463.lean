import ImbalancedChen.Certificates.PairedV2StripFiniteAssembly
import ImbalancedChen.Certificates.PairedV2StripCertificate463Left
import ImbalancedChen.Certificates.PairedV2StripCertificate463Right

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip463_checked : ∀ j : Fin (512 - firstU (⟨137, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨137, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨137, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  exact StripAssembly.forallFinCastAdd (a := 70) (b := 70)
    strip463_row_count
    (fun j => (makeCertificate (⟨(⟨137, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨137, by decide⟩ : Fin 186), j⟩ : Row))).check = true)
    strip463_checked_left strip463_checked_right

end ImbalancedChen.Certificates.PairedV2.FullMask
