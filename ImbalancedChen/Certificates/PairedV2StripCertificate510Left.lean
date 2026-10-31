import ImbalancedChen.Certificates.PairedV2StripFiniteAssembly
import ImbalancedChen.Certificates.PairedV2StripCertificate510LeftA
import ImbalancedChen.Certificates.PairedV2StripCertificate510LeftB

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip510_checked_left : ∀ j : Fin 95,
    (makeCertificate (⟨(⟨184, by decide⟩ : Fin 186), Fin.cast strip510_row_count.symm (Fin.castAdd 95 j)⟩ : Row) (approximation (⟨(⟨184, by decide⟩ : Fin 186), Fin.cast strip510_row_count.symm (Fin.castAdd 95 j)⟩ : Row))).check = true := by
  exact StripAssembly.forallFinAdd (a := 47) (b := 48)
    (fun j => (makeCertificate (⟨(⟨184, by decide⟩ : Fin 186), Fin.cast strip510_row_count.symm (Fin.castAdd 95 j)⟩ : Row) (approximation (⟨(⟨184, by decide⟩ : Fin 186), Fin.cast strip510_row_count.symm (Fin.castAdd 95 j)⟩ : Row))).check = true)
    strip510_checked_left_a strip510_checked_left_b

end ImbalancedChen.Certificates.PairedV2.FullMask
