import ImbalancedChen.Certificates.PairedV2StripFiniteAssembly
import ImbalancedChen.Certificates.PairedV2StripCertificate407Left
import ImbalancedChen.Certificates.PairedV2StripCertificate407Right

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip407_checked : ∀ j : Fin (512 - firstU (⟨81, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨81, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨81, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  exact StripAssembly.forallFinCastAdd (a := 41) (b := 41)
    strip407_row_count
    (fun j => (makeCertificate (⟨(⟨81, by decide⟩ : Fin 186), j⟩ : Row)
      (approximation (⟨(⟨81, by decide⟩ : Fin 186), j⟩ : Row))).check = true)
    strip407_checked_left strip407_checked_right

end ImbalancedChen.Certificates.PairedV2.FullMask
