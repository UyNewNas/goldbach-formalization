import ImbalancedChen.Certificates.PairedV2StripFiniteAssembly
import ImbalancedChen.Certificates.PairedV2StripCertificate507RightA
import ImbalancedChen.Certificates.PairedV2StripCertificate507RightB

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip507_checked_right : ∀ j : Fin 94,
    (makeCertificate (⟨(⟨181, by decide⟩ : Fin 186), Fin.cast strip507_row_count.symm (Fin.natAdd 93 j)⟩ : Row) (approximation (⟨(⟨181, by decide⟩ : Fin 186), Fin.cast strip507_row_count.symm (Fin.natAdd 93 j)⟩ : Row))).check = true := by
  exact StripAssembly.forallFinAdd (a := 47) (b := 47)
    (fun j => (makeCertificate (⟨(⟨181, by decide⟩ : Fin 186), Fin.cast strip507_row_count.symm (Fin.natAdd 93 j)⟩ : Row) (approximation (⟨(⟨181, by decide⟩ : Fin 186), Fin.cast strip507_row_count.symm (Fin.natAdd 93 j)⟩ : Row))).check = true)
    strip507_checked_right_a strip507_checked_right_b

end ImbalancedChen.Certificates.PairedV2.FullMask
