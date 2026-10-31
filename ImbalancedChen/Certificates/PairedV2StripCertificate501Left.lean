import ImbalancedChen.Certificates.PairedV2StripFiniteAssembly
import ImbalancedChen.Certificates.PairedV2StripCertificate501LeftA
import ImbalancedChen.Certificates.PairedV2StripCertificate501LeftB

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip501_checked_left : ∀ j : Fin 90,
    (makeCertificate (⟨(⟨175, by decide⟩ : Fin 186), Fin.cast strip501_row_count.symm (Fin.castAdd 90 j)⟩ : Row) (approximation (⟨(⟨175, by decide⟩ : Fin 186), Fin.cast strip501_row_count.symm (Fin.castAdd 90 j)⟩ : Row))).check = true := by
  exact StripAssembly.forallFinAdd (a := 45) (b := 45)
    (fun j => (makeCertificate (⟨(⟨175, by decide⟩ : Fin 186), Fin.cast strip501_row_count.symm (Fin.castAdd 90 j)⟩ : Row) (approximation (⟨(⟨175, by decide⟩ : Fin 186), Fin.cast strip501_row_count.symm (Fin.castAdd 90 j)⟩ : Row))).check = true)
    strip501_checked_left_a strip501_checked_left_b

end ImbalancedChen.Certificates.PairedV2.FullMask
