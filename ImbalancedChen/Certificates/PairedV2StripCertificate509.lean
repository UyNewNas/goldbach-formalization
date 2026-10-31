import ImbalancedChen.Certificates.PairedV2StripFiniteAssembly
import ImbalancedChen.Certificates.PairedV2StripCertificate509Left
import ImbalancedChen.Certificates.PairedV2StripCertificate509Right

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip509_checked : ∀ j : Fin (512 - firstU (⟨183, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨183, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨183, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  exact StripAssembly.forallFinCastAdd (a := 94) (b := 95)
    strip509_row_count
    (fun j => (makeCertificate (⟨(⟨183, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨183, by decide⟩ : Fin 186), j⟩ : Row))).check = true)
    strip509_checked_left strip509_checked_right

end ImbalancedChen.Certificates.PairedV2.FullMask
