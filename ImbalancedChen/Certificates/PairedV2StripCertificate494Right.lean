import ImbalancedChen.Certificates.PairedV2StripFiniteAssembly
import ImbalancedChen.Certificates.PairedV2StripCertificate494RightA
import ImbalancedChen.Certificates.PairedV2StripCertificate494RightB

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip494_checked_right : ∀ j : Fin 87,
    (makeCertificate (⟨(⟨168, by decide⟩ : Fin 186), Fin.cast strip494_row_count.symm (Fin.natAdd 86 j)⟩ : Row) (approximation (⟨(⟨168, by decide⟩ : Fin 186), Fin.cast strip494_row_count.symm (Fin.natAdd 86 j)⟩ : Row))).check = true := by
  exact StripAssembly.forallFinAdd (a := 43) (b := 44)
    (fun j => (makeCertificate (⟨(⟨168, by decide⟩ : Fin 186), Fin.cast strip494_row_count.symm (Fin.natAdd 86 j)⟩ : Row) (approximation (⟨(⟨168, by decide⟩ : Fin 186), Fin.cast strip494_row_count.symm (Fin.natAdd 86 j)⟩ : Row))).check = true)
    strip494_checked_right_a strip494_checked_right_b

end ImbalancedChen.Certificates.PairedV2.FullMask
