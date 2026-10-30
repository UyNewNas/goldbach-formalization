import ImbalancedChen.Certificates.PairedV2StripFiniteAssembly
import ImbalancedChen.Certificates.PairedV2StripCertificate425Left
import ImbalancedChen.Certificates.PairedV2StripCertificate425Right

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip425_checked : ∀ j : Fin (512 - firstU (⟨99, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨99, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨99, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  exact StripAssembly.forallFinCastAdd (a := 50) (b := 51)
    strip425_row_count
    (fun j => (makeCertificate (⟨(⟨99, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨99, by decide⟩ : Fin 186), j⟩ : Row))).check = true)
    strip425_checked_left strip425_checked_right

end ImbalancedChen.Certificates.PairedV2.FullMask
