import ImbalancedChen.Certificates.PairedV2StripFiniteAssembly
import ImbalancedChen.Certificates.PairedV2StripCertificate421Left
import ImbalancedChen.Certificates.PairedV2StripCertificate421Right

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip421_checked : ∀ j : Fin (512 - firstU (⟨95, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨95, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨95, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  exact StripAssembly.forallFinCastAdd (a := 48) (b := 48)
    strip421_row_count
    (fun j => (makeCertificate (⟨(⟨95, by decide⟩ : Fin 186), j⟩ : Row)
      (approximation (⟨(⟨95, by decide⟩ : Fin 186), j⟩ : Row))).check = true)
    strip421_checked_left strip421_checked_right

end ImbalancedChen.Certificates.PairedV2.FullMask
