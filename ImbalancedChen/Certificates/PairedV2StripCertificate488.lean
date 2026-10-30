import ImbalancedChen.Certificates.PairedV2StripFiniteAssembly
import ImbalancedChen.Certificates.PairedV2StripCertificate488Left
import ImbalancedChen.Certificates.PairedV2StripCertificate488Right

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip488_checked : ∀ j : Fin (512 - firstU (⟨162, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨162, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨162, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  exact StripAssembly.forallFinCastAdd (a := 83) (b := 83)
    strip488_row_count
    (fun j => (makeCertificate (⟨(⟨162, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨162, by decide⟩ : Fin 186), j⟩ : Row))).check = true)
    strip488_checked_left strip488_checked_right

end ImbalancedChen.Certificates.PairedV2.FullMask
