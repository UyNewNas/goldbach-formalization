import ImbalancedChen.Certificates.PairedV2StripFiniteAssembly
import ImbalancedChen.Certificates.PairedV2StripCertificate440Left
import ImbalancedChen.Certificates.PairedV2StripCertificate440Right

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip440_checked : ∀ j : Fin (512 - firstU (⟨114, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨114, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨114, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  exact StripAssembly.forallFinCastAdd (a := 58) (b := 58)
    strip440_row_count
    (fun j => (makeCertificate (⟨(⟨114, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨114, by decide⟩ : Fin 186), j⟩ : Row))).check = true)
    strip440_checked_left strip440_checked_right

end ImbalancedChen.Certificates.PairedV2.FullMask
