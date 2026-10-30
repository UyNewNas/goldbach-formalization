import ImbalancedChen.Certificates.PairedV2StripFiniteAssembly
import ImbalancedChen.Certificates.PairedV2StripCertificate502Left
import ImbalancedChen.Certificates.PairedV2StripCertificate502Right

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip502_checked : ∀ j : Fin (512 - firstU (⟨176, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨176, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨176, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  exact StripAssembly.forallFinCastAdd (a := 90) (b := 91)
    strip502_row_count
    (fun j => (makeCertificate (⟨(⟨176, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨176, by decide⟩ : Fin 186), j⟩ : Row))).check = true)
    strip502_checked_left strip502_checked_right

end ImbalancedChen.Certificates.PairedV2.FullMask
