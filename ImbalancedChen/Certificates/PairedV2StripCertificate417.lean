import ImbalancedChen.Certificates.PairedV2StripFiniteAssembly
import ImbalancedChen.Certificates.PairedV2StripCertificate417Left
import ImbalancedChen.Certificates.PairedV2StripCertificate417Right

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip417_checked : ∀ j : Fin (512 - firstU (⟨91, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨91, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨91, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  exact StripAssembly.forallFinCastAdd (a := 46) (b := 46)
    strip417_row_count
    (fun j => (makeCertificate (⟨(⟨91, by decide⟩ : Fin 186), j⟩ : Row)
      (approximation (⟨(⟨91, by decide⟩ : Fin 186), j⟩ : Row))).check = true)
    strip417_checked_left strip417_checked_right

end ImbalancedChen.Certificates.PairedV2.FullMask
