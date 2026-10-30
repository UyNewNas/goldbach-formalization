import ImbalancedChen.Certificates.PairedV2StripFiniteAssembly
import ImbalancedChen.Certificates.PairedV2StripCertificate474Left
import ImbalancedChen.Certificates.PairedV2StripCertificate474Right

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip474_checked : ∀ j : Fin (512 - firstU (⟨148, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨148, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨148, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  exact StripAssembly.forallFinCastAdd (a := 76) (b := 76)
    strip474_row_count
    (fun j => (makeCertificate (⟨(⟨148, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨148, by decide⟩ : Fin 186), j⟩ : Row))).check = true)
    strip474_checked_left strip474_checked_right

end ImbalancedChen.Certificates.PairedV2.FullMask
