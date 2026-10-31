import ImbalancedChen.Certificates.PairedV2StripFiniteAssembly
import ImbalancedChen.Certificates.PairedV2StripCertificate484RightA
import ImbalancedChen.Certificates.PairedV2StripCertificate484RightB

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip484_checked_right : ∀ j : Fin 81,
    (makeCertificate (⟨(⟨158, by decide⟩ : Fin 186), Fin.cast strip484_row_count.symm (Fin.natAdd 81 j)⟩ : Row) (approximation (⟨(⟨158, by decide⟩ : Fin 186), Fin.cast strip484_row_count.symm (Fin.natAdd 81 j)⟩ : Row))).check = true := by
  exact StripAssembly.forallFinAdd (a := 40) (b := 41)
    (fun j => (makeCertificate (⟨(⟨158, by decide⟩ : Fin 186), Fin.cast strip484_row_count.symm (Fin.natAdd 81 j)⟩ : Row) (approximation (⟨(⟨158, by decide⟩ : Fin 186), Fin.cast strip484_row_count.symm (Fin.natAdd 81 j)⟩ : Row))).check = true)
    strip484_checked_right_a strip484_checked_right_b

end ImbalancedChen.Certificates.PairedV2.FullMask
