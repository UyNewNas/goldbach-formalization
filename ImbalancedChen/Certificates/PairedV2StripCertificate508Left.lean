import ImbalancedChen.Certificates.PairedV2StripFiniteAssembly
import ImbalancedChen.Certificates.PairedV2StripCertificate508LeftA
import ImbalancedChen.Certificates.PairedV2StripCertificate508LeftB

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip508_checked_left : ∀ j : Fin 94,
    (makeCertificate (⟨(⟨182, by decide⟩ : Fin 186), Fin.cast strip508_row_count.symm (Fin.castAdd 94 j)⟩ : Row) (approximation (⟨(⟨182, by decide⟩ : Fin 186), Fin.cast strip508_row_count.symm (Fin.castAdd 94 j)⟩ : Row))).check = true := by
  exact StripAssembly.forallFinAdd (a := 47) (b := 47)
    (fun j => (makeCertificate (⟨(⟨182, by decide⟩ : Fin 186), Fin.cast strip508_row_count.symm (Fin.castAdd 94 j)⟩ : Row) (approximation (⟨(⟨182, by decide⟩ : Fin 186), Fin.cast strip508_row_count.symm (Fin.castAdd 94 j)⟩ : Row))).check = true)
    strip508_checked_left_a strip508_checked_left_b

end ImbalancedChen.Certificates.PairedV2.FullMask
