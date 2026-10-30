import ImbalancedChen.Certificates.PairedV2StripFiniteAssembly
import ImbalancedChen.Certificates.PairedV2StripCertificate452Left
import ImbalancedChen.Certificates.PairedV2StripCertificate452Right

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip452_checked : ∀ j : Fin (512 - firstU (⟨126, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨126, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨126, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  exact StripAssembly.forallFinCastAdd (a := 64) (b := 65)
    strip452_row_count
    (fun j => (makeCertificate (⟨(⟨126, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨126, by decide⟩ : Fin 186), j⟩ : Row))).check = true)
    strip452_checked_left strip452_checked_right

end ImbalancedChen.Certificates.PairedV2.FullMask
