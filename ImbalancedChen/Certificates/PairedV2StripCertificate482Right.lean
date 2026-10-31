import ImbalancedChen.Certificates.PairedV2StripFiniteAssembly
import ImbalancedChen.Certificates.PairedV2StripCertificate482RightA
import ImbalancedChen.Certificates.PairedV2StripCertificate482RightB

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip482_checked_right : ∀ j : Fin 80,
    (makeCertificate (⟨(⟨156, by decide⟩ : Fin 186), Fin.cast strip482_row_count.symm (Fin.natAdd 80 j)⟩ : Row) (approximation (⟨(⟨156, by decide⟩ : Fin 186), Fin.cast strip482_row_count.symm (Fin.natAdd 80 j)⟩ : Row))).check = true := by
  exact StripAssembly.forallFinAdd (a := 40) (b := 40)
    (fun j => (makeCertificate (⟨(⟨156, by decide⟩ : Fin 186), Fin.cast strip482_row_count.symm (Fin.natAdd 80 j)⟩ : Row) (approximation (⟨(⟨156, by decide⟩ : Fin 186), Fin.cast strip482_row_count.symm (Fin.natAdd 80 j)⟩ : Row))).check = true)
    strip482_checked_right_a strip482_checked_right_b

end ImbalancedChen.Certificates.PairedV2.FullMask
