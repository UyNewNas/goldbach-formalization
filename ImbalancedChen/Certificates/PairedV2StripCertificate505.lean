import ImbalancedChen.Certificates.PairedV2StripFiniteAssembly
import ImbalancedChen.Certificates.PairedV2StripCertificate505Left
import ImbalancedChen.Certificates.PairedV2StripCertificate505Right

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip505_checked : ∀ j : Fin (512 - firstU (⟨179, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨179, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨179, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  exact StripAssembly.forallFinCastAdd (a := 92) (b := 92)
    strip505_row_count
    (fun j => (makeCertificate (⟨(⟨179, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨179, by decide⟩ : Fin 186), j⟩ : Row))).check = true)
    strip505_checked_left strip505_checked_right

end ImbalancedChen.Certificates.PairedV2.FullMask
