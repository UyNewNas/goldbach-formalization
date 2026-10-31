import ImbalancedChen.Certificates.PairedV2StripFiniteAssembly
import ImbalancedChen.Certificates.PairedV2StripCertificate511Left
import ImbalancedChen.Certificates.PairedV2StripCertificate511Right

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip511_checked : ∀ j : Fin (512 - firstU (⟨185, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨185, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨185, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  exact StripAssembly.forallFinCastAdd (a := 95) (b := 96)
    strip511_row_count
    (fun j => (makeCertificate (⟨(⟨185, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨185, by decide⟩ : Fin 186), j⟩ : Row))).check = true)
    strip511_checked_left strip511_checked_right

end ImbalancedChen.Certificates.PairedV2.FullMask
