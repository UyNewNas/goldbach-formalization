import ImbalancedChen.Certificates.PairedV2StripFiniteAssembly
import ImbalancedChen.Certificates.PairedV2StripCertificate418Left
import ImbalancedChen.Certificates.PairedV2StripCertificate418Right

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip418_checked : ∀ j : Fin (512 - firstU (⟨92, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨92, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨92, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  exact StripAssembly.forallFinCastAdd (a := 46) (b := 47)
    strip418_row_count
    (fun j => (makeCertificate (⟨(⟨92, by decide⟩ : Fin 186), j⟩ : Row)
      (approximation (⟨(⟨92, by decide⟩ : Fin 186), j⟩ : Row))).check = true)
    strip418_checked_left strip418_checked_right

end ImbalancedChen.Certificates.PairedV2.FullMask
