import ImbalancedChen.Certificates.PairedV2StripFiniteAssembly
import ImbalancedChen.Certificates.PairedV2StripCertificate504Left
import ImbalancedChen.Certificates.PairedV2StripCertificate504Right

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip504_checked : ∀ j : Fin (512 - firstU (⟨178, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨178, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨178, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  exact StripAssembly.forallFinCastAdd (a := 91) (b := 92)
    strip504_row_count
    (fun j => (makeCertificate (⟨(⟨178, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨178, by decide⟩ : Fin 186), j⟩ : Row))).check = true)
    strip504_checked_left strip504_checked_right

end ImbalancedChen.Certificates.PairedV2.FullMask
