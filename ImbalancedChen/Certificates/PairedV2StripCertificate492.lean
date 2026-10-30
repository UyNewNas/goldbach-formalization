import ImbalancedChen.Certificates.PairedV2StripFiniteAssembly
import ImbalancedChen.Certificates.PairedV2StripCertificate492Left
import ImbalancedChen.Certificates.PairedV2StripCertificate492Right

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip492_checked : ∀ j : Fin (512 - firstU (⟨166, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨166, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨166, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  exact StripAssembly.forallFinCastAdd (a := 85) (b := 86)
    strip492_row_count
    (fun j => (makeCertificate (⟨(⟨166, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨166, by decide⟩ : Fin 186), j⟩ : Row))).check = true)
    strip492_checked_left strip492_checked_right

end ImbalancedChen.Certificates.PairedV2.FullMask
