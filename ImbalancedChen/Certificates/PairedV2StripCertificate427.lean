import ImbalancedChen.Certificates.PairedV2StripFiniteAssembly
import ImbalancedChen.Certificates.PairedV2StripCertificate427Left
import ImbalancedChen.Certificates.PairedV2StripCertificate427Right

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip427_checked : ∀ j : Fin (512 - firstU (⟨101, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨101, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨101, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  exact StripAssembly.forallFinCastAdd (a := 51) (b := 52)
    strip427_row_count
    (fun j => (makeCertificate (⟨(⟨101, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨101, by decide⟩ : Fin 186), j⟩ : Row))).check = true)
    strip427_checked_left strip427_checked_right

end ImbalancedChen.Certificates.PairedV2.FullMask
