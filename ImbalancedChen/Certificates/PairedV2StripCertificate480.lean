import ImbalancedChen.Certificates.PairedV2StripFiniteAssembly
import ImbalancedChen.Certificates.PairedV2StripCertificate480Left
import ImbalancedChen.Certificates.PairedV2StripCertificate480Right

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip480_checked : ∀ j : Fin (512 - firstU (⟨154, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨154, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨154, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  exact StripAssembly.forallFinCastAdd (a := 79) (b := 79)
    strip480_row_count
    (fun j => (makeCertificate (⟨(⟨154, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨154, by decide⟩ : Fin 186), j⟩ : Row))).check = true)
    strip480_checked_left strip480_checked_right

end ImbalancedChen.Certificates.PairedV2.FullMask
