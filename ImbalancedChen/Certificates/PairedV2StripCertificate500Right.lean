import ImbalancedChen.Certificates.PairedV2StripFiniteAssembly
import ImbalancedChen.Certificates.PairedV2StripCertificate500RightA
import ImbalancedChen.Certificates.PairedV2StripCertificate500RightB

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip500_checked_right : ∀ j : Fin 90,
    (makeCertificate (⟨(⟨174, by decide⟩ : Fin 186), Fin.cast strip500_row_count.symm (Fin.natAdd 89 j)⟩ : Row) (approximation (⟨(⟨174, by decide⟩ : Fin 186), Fin.cast strip500_row_count.symm (Fin.natAdd 89 j)⟩ : Row))).check = true := by
  exact StripAssembly.forallFinAdd (a := 45) (b := 45)
    (fun j => (makeCertificate (⟨(⟨174, by decide⟩ : Fin 186), Fin.cast strip500_row_count.symm (Fin.natAdd 89 j)⟩ : Row) (approximation (⟨(⟨174, by decide⟩ : Fin 186), Fin.cast strip500_row_count.symm (Fin.natAdd 89 j)⟩ : Row))).check = true)
    strip500_checked_right_a strip500_checked_right_b

end ImbalancedChen.Certificates.PairedV2.FullMask
