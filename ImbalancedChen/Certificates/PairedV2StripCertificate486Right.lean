import ImbalancedChen.Certificates.PairedV2StripFiniteAssembly
import ImbalancedChen.Certificates.PairedV2StripCertificate486RightA
import ImbalancedChen.Certificates.PairedV2StripCertificate486RightB

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip486_checked_right : ∀ j : Fin 82,
    (makeCertificate (⟨(⟨160, by decide⟩ : Fin 186), Fin.cast strip486_row_count.symm (Fin.natAdd 82 j)⟩ : Row) (approximation (⟨(⟨160, by decide⟩ : Fin 186), Fin.cast strip486_row_count.symm (Fin.natAdd 82 j)⟩ : Row))).check = true := by
  exact StripAssembly.forallFinAdd (a := 41) (b := 41)
    (fun j => (makeCertificate (⟨(⟨160, by decide⟩ : Fin 186), Fin.cast strip486_row_count.symm (Fin.natAdd 82 j)⟩ : Row) (approximation (⟨(⟨160, by decide⟩ : Fin 186), Fin.cast strip486_row_count.symm (Fin.natAdd 82 j)⟩ : Row))).check = true)
    strip486_checked_right_a strip486_checked_right_b

end ImbalancedChen.Certificates.PairedV2.FullMask
