import ImbalancedChen.Certificates.PairedV2StripFiniteAssembly
import ImbalancedChen.Certificates.PairedV2StripCertificate430Left
import ImbalancedChen.Certificates.PairedV2StripCertificate430Right

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip430_checked : ∀ j : Fin (512 - firstU (⟨104, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨104, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨104, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  exact StripAssembly.forallFinCastAdd (a := 53) (b := 53)
    strip430_row_count
    (fun j => (makeCertificate (⟨(⟨104, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨104, by decide⟩ : Fin 186), j⟩ : Row))).check = true)
    strip430_checked_left strip430_checked_right

end ImbalancedChen.Certificates.PairedV2.FullMask
