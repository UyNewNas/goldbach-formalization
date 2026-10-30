import ImbalancedChen.Certificates.PairedV2StripFiniteAssembly
import ImbalancedChen.Certificates.PairedV2StripCertificate416Left
import ImbalancedChen.Certificates.PairedV2StripCertificate416Right

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip416_checked : ∀ j : Fin (512 - firstU (⟨90, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨90, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨90, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  exact StripAssembly.forallFinCastAdd (a := 45) (b := 46)
    strip416_row_count
    (fun j => (makeCertificate (⟨(⟨90, by decide⟩ : Fin 186), j⟩ : Row)
      (approximation (⟨(⟨90, by decide⟩ : Fin 186), j⟩ : Row))).check = true)
    strip416_checked_left strip416_checked_right

end ImbalancedChen.Certificates.PairedV2.FullMask
