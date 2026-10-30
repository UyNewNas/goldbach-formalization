import ImbalancedChen.Certificates.PairedV2StripFiniteAssembly
import ImbalancedChen.Certificates.PairedV2StripCertificate475Left
import ImbalancedChen.Certificates.PairedV2StripCertificate475Right

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip475_checked : ∀ j : Fin (512 - firstU (⟨149, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨149, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨149, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  exact StripAssembly.forallFinCastAdd (a := 76) (b := 77)
    strip475_row_count
    (fun j => (makeCertificate (⟨(⟨149, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨149, by decide⟩ : Fin 186), j⟩ : Row))).check = true)
    strip475_checked_left strip475_checked_right

end ImbalancedChen.Certificates.PairedV2.FullMask
