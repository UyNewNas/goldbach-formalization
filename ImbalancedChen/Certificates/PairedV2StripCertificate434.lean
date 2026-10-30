import ImbalancedChen.Certificates.PairedV2StripFiniteAssembly
import ImbalancedChen.Certificates.PairedV2StripCertificate434Left
import ImbalancedChen.Certificates.PairedV2StripCertificate434Right

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip434_checked : ∀ j : Fin (512 - firstU (⟨108, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨108, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨108, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  exact StripAssembly.forallFinCastAdd (a := 55) (b := 55)
    strip434_row_count
    (fun j => (makeCertificate (⟨(⟨108, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨108, by decide⟩ : Fin 186), j⟩ : Row))).check = true)
    strip434_checked_left strip434_checked_right

end ImbalancedChen.Certificates.PairedV2.FullMask
