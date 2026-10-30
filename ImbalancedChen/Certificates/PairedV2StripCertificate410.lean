import ImbalancedChen.Certificates.PairedV2StripFiniteAssembly
import ImbalancedChen.Certificates.PairedV2StripCertificate410Left
import ImbalancedChen.Certificates.PairedV2StripCertificate410Right

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip410_checked : ∀ j : Fin (512 - firstU (⟨84, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨84, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨84, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  exact StripAssembly.forallFinCastAdd (a := 42) (b := 43)
    strip410_row_count
    (fun j => (makeCertificate (⟨(⟨84, by decide⟩ : Fin 186), j⟩ : Row)
      (approximation (⟨(⟨84, by decide⟩ : Fin 186), j⟩ : Row))).check = true)
    strip410_checked_left strip410_checked_right

end ImbalancedChen.Certificates.PairedV2.FullMask
