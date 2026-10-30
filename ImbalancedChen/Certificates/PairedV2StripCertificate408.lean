import ImbalancedChen.Certificates.PairedV2StripFiniteAssembly
import ImbalancedChen.Certificates.PairedV2StripCertificate408Left
import ImbalancedChen.Certificates.PairedV2StripCertificate408Right

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip408_checked : ∀ j : Fin (512 - firstU (⟨82, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨82, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨82, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  exact StripAssembly.forallFinCastAdd (a := 41) (b := 42)
    strip408_row_count
    (fun j => (makeCertificate (⟨(⟨82, by decide⟩ : Fin 186), j⟩ : Row)
      (approximation (⟨(⟨82, by decide⟩ : Fin 186), j⟩ : Row))).check = true)
    strip408_checked_left strip408_checked_right

end ImbalancedChen.Certificates.PairedV2.FullMask
