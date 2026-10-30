import ImbalancedChen.Certificates.PairedV2StripFiniteAssembly
import ImbalancedChen.Certificates.PairedV2StripCertificate500Left
import ImbalancedChen.Certificates.PairedV2StripCertificate500Right

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip500_checked : ∀ j : Fin (512 - firstU (⟨174, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨174, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨174, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  exact StripAssembly.forallFinCastAdd (a := 89) (b := 90)
    strip500_row_count
    (fun j => (makeCertificate (⟨(⟨174, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨174, by decide⟩ : Fin 186), j⟩ : Row))).check = true)
    strip500_checked_left strip500_checked_right

end ImbalancedChen.Certificates.PairedV2.FullMask
