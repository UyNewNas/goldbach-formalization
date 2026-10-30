import ImbalancedChen.Certificates.PairedV2StripFiniteAssembly
import ImbalancedChen.Certificates.PairedV2StripCertificate441Left
import ImbalancedChen.Certificates.PairedV2StripCertificate441Right

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip441_checked : ∀ j : Fin (512 - firstU (⟨115, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨115, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨115, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  exact StripAssembly.forallFinCastAdd (a := 58) (b := 59)
    strip441_row_count
    (fun j => (makeCertificate (⟨(⟨115, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨115, by decide⟩ : Fin 186), j⟩ : Row))).check = true)
    strip441_checked_left strip441_checked_right

end ImbalancedChen.Certificates.PairedV2.FullMask
