import ImbalancedChen.Certificates.PairedV2StripFiniteAssembly
import ImbalancedChen.Certificates.PairedV2StripCertificate479RightA
import ImbalancedChen.Certificates.PairedV2StripCertificate479RightB

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip479_checked_right : ∀ j : Fin 79,
    (makeCertificate (⟨(⟨153, by decide⟩ : Fin 186), Fin.cast strip479_row_count.symm (Fin.natAdd 78 j)⟩ : Row) (approximation (⟨(⟨153, by decide⟩ : Fin 186), Fin.cast strip479_row_count.symm (Fin.natAdd 78 j)⟩ : Row))).check = true := by
  exact StripAssembly.forallFinAdd (a := 39) (b := 40)
    (fun j => (makeCertificate (⟨(⟨153, by decide⟩ : Fin 186), Fin.cast strip479_row_count.symm (Fin.natAdd 78 j)⟩ : Row) (approximation (⟨(⟨153, by decide⟩ : Fin 186), Fin.cast strip479_row_count.symm (Fin.natAdd 78 j)⟩ : Row))).check = true)
    strip479_checked_right_a strip479_checked_right_b

end ImbalancedChen.Certificates.PairedV2.FullMask
