import ImbalancedChen.Certificates.PairedV2StripFiniteAssembly
import ImbalancedChen.Certificates.PairedV2StripCertificate429Left
import ImbalancedChen.Certificates.PairedV2StripCertificate429Right

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip429_checked : ∀ j : Fin (512 - firstU (⟨103, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨103, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨103, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  exact StripAssembly.forallFinCastAdd (a := 52) (b := 53)
    strip429_row_count
    (fun j => (makeCertificate (⟨(⟨103, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨103, by decide⟩ : Fin 186), j⟩ : Row))).check = true)
    strip429_checked_left strip429_checked_right

end ImbalancedChen.Certificates.PairedV2.FullMask
