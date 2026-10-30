import ImbalancedChen.Certificates.PairedV2StripFiniteAssembly
import ImbalancedChen.Certificates.PairedV2StripCertificate487Left
import ImbalancedChen.Certificates.PairedV2StripCertificate487Right

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip487_checked : ∀ j : Fin (512 - firstU (⟨161, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨161, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨161, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  exact StripAssembly.forallFinCastAdd (a := 82) (b := 83)
    strip487_row_count
    (fun j => (makeCertificate (⟨(⟨161, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨161, by decide⟩ : Fin 186), j⟩ : Row))).check = true)
    strip487_checked_left strip487_checked_right

end ImbalancedChen.Certificates.PairedV2.FullMask
