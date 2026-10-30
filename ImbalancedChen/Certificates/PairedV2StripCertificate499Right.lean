import ImbalancedChen.Certificates.PairedV2StripFiniteAssembly
import ImbalancedChen.Certificates.PairedV2StripCertificate499RightA
import ImbalancedChen.Certificates.PairedV2StripCertificate499RightB

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip499_checked_right : ∀ j : Fin 89,
    (makeCertificate (⟨(⟨173, by decide⟩ : Fin 186), Fin.cast strip499_row_count.symm (Fin.natAdd 89 j)⟩ : Row) (approximation (⟨(⟨173, by decide⟩ : Fin 186), Fin.cast strip499_row_count.symm (Fin.natAdd 89 j)⟩ : Row))).check = true := by
  exact StripAssembly.forallFinAdd (a := 44) (b := 45)
    (fun j => (makeCertificate (⟨(⟨173, by decide⟩ : Fin 186), Fin.cast strip499_row_count.symm (Fin.natAdd 89 j)⟩ : Row) (approximation (⟨(⟨173, by decide⟩ : Fin 186), Fin.cast strip499_row_count.symm (Fin.natAdd 89 j)⟩ : Row))).check = true)
    strip499_checked_right_a strip499_checked_right_b

end ImbalancedChen.Certificates.PairedV2.FullMask
