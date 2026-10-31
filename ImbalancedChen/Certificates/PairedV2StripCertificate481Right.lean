import ImbalancedChen.Certificates.PairedV2StripFiniteAssembly
import ImbalancedChen.Certificates.PairedV2StripCertificate481RightA
import ImbalancedChen.Certificates.PairedV2StripCertificate481RightB

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip481_checked_right : ∀ j : Fin 80,
    (makeCertificate (⟨(⟨155, by decide⟩ : Fin 186), Fin.cast strip481_row_count.symm (Fin.natAdd 79 j)⟩ : Row) (approximation (⟨(⟨155, by decide⟩ : Fin 186), Fin.cast strip481_row_count.symm (Fin.natAdd 79 j)⟩ : Row))).check = true := by
  exact StripAssembly.forallFinAdd (a := 40) (b := 40)
    (fun j => (makeCertificate (⟨(⟨155, by decide⟩ : Fin 186), Fin.cast strip481_row_count.symm (Fin.natAdd 79 j)⟩ : Row) (approximation (⟨(⟨155, by decide⟩ : Fin 186), Fin.cast strip481_row_count.symm (Fin.natAdd 79 j)⟩ : Row))).check = true)
    strip481_checked_right_a strip481_checked_right_b

end ImbalancedChen.Certificates.PairedV2.FullMask
