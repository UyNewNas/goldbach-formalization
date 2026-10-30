import ImbalancedChen.Certificates.PairedV2StripFiniteAssembly
import ImbalancedChen.Certificates.PairedV2StripCertificate411Left
import ImbalancedChen.Certificates.PairedV2StripCertificate411Right

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip411_checked : ∀ j : Fin (512 - firstU (⟨85, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨85, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨85, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  exact StripAssembly.forallFinCastAdd (a := 43) (b := 43)
    strip411_row_count
    (fun j => (makeCertificate (⟨(⟨85, by decide⟩ : Fin 186), j⟩ : Row)
      (approximation (⟨(⟨85, by decide⟩ : Fin 186), j⟩ : Row))).check = true)
    strip411_checked_left strip411_checked_right

end ImbalancedChen.Certificates.PairedV2.FullMask
