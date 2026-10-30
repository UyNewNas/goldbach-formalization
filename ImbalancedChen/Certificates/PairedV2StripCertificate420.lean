import ImbalancedChen.Certificates.PairedV2StripFiniteAssembly
import ImbalancedChen.Certificates.PairedV2StripCertificate420Left
import ImbalancedChen.Certificates.PairedV2StripCertificate420Right

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip420_checked : ∀ j : Fin (512 - firstU (⟨94, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨94, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨94, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  exact StripAssembly.forallFinCastAdd (a := 47) (b := 48)
    strip420_row_count
    (fun j => (makeCertificate (⟨(⟨94, by decide⟩ : Fin 186), j⟩ : Row)
      (approximation (⟨(⟨94, by decide⟩ : Fin 186), j⟩ : Row))).check = true)
    strip420_checked_left strip420_checked_right

end ImbalancedChen.Certificates.PairedV2.FullMask
