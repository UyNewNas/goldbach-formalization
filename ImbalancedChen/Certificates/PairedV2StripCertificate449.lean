import ImbalancedChen.Certificates.PairedV2StripFiniteAssembly
import ImbalancedChen.Certificates.PairedV2StripCertificate449Left
import ImbalancedChen.Certificates.PairedV2StripCertificate449Right

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip449_checked : ∀ j : Fin (512 - firstU (⟨123, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨123, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨123, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  exact StripAssembly.forallFinCastAdd (a := 62) (b := 63)
    strip449_row_count
    (fun j => (makeCertificate (⟨(⟨123, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨123, by decide⟩ : Fin 186), j⟩ : Row))).check = true)
    strip449_checked_left strip449_checked_right

end ImbalancedChen.Certificates.PairedV2.FullMask
