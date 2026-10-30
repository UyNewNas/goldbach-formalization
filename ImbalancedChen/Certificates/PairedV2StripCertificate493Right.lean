import ImbalancedChen.Certificates.PairedV2StripFiniteAssembly
import ImbalancedChen.Certificates.PairedV2StripCertificate493RightA
import ImbalancedChen.Certificates.PairedV2StripCertificate493RightB

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip493_checked_right : ∀ j : Fin 86,
    (makeCertificate (⟨(⟨167, by decide⟩ : Fin 186), Fin.cast strip493_row_count.symm (Fin.natAdd 86 j)⟩ : Row) (approximation (⟨(⟨167, by decide⟩ : Fin 186), Fin.cast strip493_row_count.symm (Fin.natAdd 86 j)⟩ : Row))).check = true := by
  exact StripAssembly.forallFinAdd (a := 43) (b := 43)
    (fun j => (makeCertificate (⟨(⟨167, by decide⟩ : Fin 186), Fin.cast strip493_row_count.symm (Fin.natAdd 86 j)⟩ : Row) (approximation (⟨(⟨167, by decide⟩ : Fin 186), Fin.cast strip493_row_count.symm (Fin.natAdd 86 j)⟩ : Row))).check = true)
    strip493_checked_right_a strip493_checked_right_b

end ImbalancedChen.Certificates.PairedV2.FullMask
