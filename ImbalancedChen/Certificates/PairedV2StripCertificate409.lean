import ImbalancedChen.Certificates.PairedV2StripFiniteAssembly
import ImbalancedChen.Certificates.PairedV2StripCertificate409Left
import ImbalancedChen.Certificates.PairedV2StripCertificate409Right

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip409_checked : ∀ j : Fin (512 - firstU (⟨83, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨83, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨83, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  exact StripAssembly.forallFinCastAdd (a := 42) (b := 42)
    strip409_row_count
    (fun j => (makeCertificate (⟨(⟨83, by decide⟩ : Fin 186), j⟩ : Row)
      (approximation (⟨(⟨83, by decide⟩ : Fin 186), j⟩ : Row))).check = true)
    strip409_checked_left strip409_checked_right

end ImbalancedChen.Certificates.PairedV2.FullMask
