import ImbalancedChen.Certificates.PairedV2StripFiniteAssembly
import ImbalancedChen.Certificates.PairedV2StripCertificate445Left
import ImbalancedChen.Certificates.PairedV2StripCertificate445Right

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip445_checked : ∀ j : Fin (512 - firstU (⟨119, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨119, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨119, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  exact StripAssembly.forallFinCastAdd (a := 60) (b := 61)
    strip445_row_count
    (fun j => (makeCertificate (⟨(⟨119, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨119, by decide⟩ : Fin 186), j⟩ : Row))).check = true)
    strip445_checked_left strip445_checked_right

end ImbalancedChen.Certificates.PairedV2.FullMask
