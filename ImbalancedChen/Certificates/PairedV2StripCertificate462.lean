import ImbalancedChen.Certificates.PairedV2StripFiniteAssembly
import ImbalancedChen.Certificates.PairedV2StripCertificate462Left
import ImbalancedChen.Certificates.PairedV2StripCertificate462Right

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip462_checked : ∀ j : Fin (512 - firstU (⟨136, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨136, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨136, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  exact StripAssembly.forallFinCastAdd (a := 69) (b := 70)
    strip462_row_count
    (fun j => (makeCertificate (⟨(⟨136, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨136, by decide⟩ : Fin 186), j⟩ : Row))).check = true)
    strip462_checked_left strip462_checked_right

end ImbalancedChen.Certificates.PairedV2.FullMask
