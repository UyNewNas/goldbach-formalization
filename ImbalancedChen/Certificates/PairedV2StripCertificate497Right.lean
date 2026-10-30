import ImbalancedChen.Certificates.PairedV2StripFiniteAssembly
import ImbalancedChen.Certificates.PairedV2StripCertificate497RightA
import ImbalancedChen.Certificates.PairedV2StripCertificate497RightB

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip497_checked_right : ∀ j : Fin 88,
    (makeCertificate (⟨(⟨171, by decide⟩ : Fin 186), Fin.cast strip497_row_count.symm (Fin.natAdd 88 j)⟩ : Row) (approximation (⟨(⟨171, by decide⟩ : Fin 186), Fin.cast strip497_row_count.symm (Fin.natAdd 88 j)⟩ : Row))).check = true := by
  exact StripAssembly.forallFinAdd (a := 44) (b := 44)
    (fun j => (makeCertificate (⟨(⟨171, by decide⟩ : Fin 186), Fin.cast strip497_row_count.symm (Fin.natAdd 88 j)⟩ : Row) (approximation (⟨(⟨171, by decide⟩ : Fin 186), Fin.cast strip497_row_count.symm (Fin.natAdd 88 j)⟩ : Row))).check = true)
    strip497_checked_right_a strip497_checked_right_b

end ImbalancedChen.Certificates.PairedV2.FullMask
