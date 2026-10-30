import ImbalancedChen.Certificates.PairedV2StripFiniteAssembly
import ImbalancedChen.Certificates.PairedV2StripCertificate464Left
import ImbalancedChen.Certificates.PairedV2StripCertificate464Right

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip464_checked : ∀ j : Fin (512 - firstU (⟨138, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨138, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨138, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  exact StripAssembly.forallFinCastAdd (a := 70) (b := 71)
    strip464_row_count
    (fun j => (makeCertificate (⟨(⟨138, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨138, by decide⟩ : Fin 186), j⟩ : Row))).check = true)
    strip464_checked_left strip464_checked_right

end ImbalancedChen.Certificates.PairedV2.FullMask
