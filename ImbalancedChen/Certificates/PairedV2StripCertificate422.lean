import ImbalancedChen.Certificates.PairedV2StripFiniteAssembly
import ImbalancedChen.Certificates.PairedV2StripCertificate422Left
import ImbalancedChen.Certificates.PairedV2StripCertificate422Right

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip422_checked : ∀ j : Fin (512 - firstU (⟨96, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨96, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨96, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  exact StripAssembly.forallFinCastAdd (a := 48) (b := 49)
    strip422_row_count
    (fun j => (makeCertificate (⟨(⟨96, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨96, by decide⟩ : Fin 186), j⟩ : Row))).check = true)
    strip422_checked_left strip422_checked_right

end ImbalancedChen.Certificates.PairedV2.FullMask
