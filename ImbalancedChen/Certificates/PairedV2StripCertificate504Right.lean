import ImbalancedChen.Certificates.PairedV2StripFiniteAssembly
import ImbalancedChen.Certificates.PairedV2StripCertificate504RightA
import ImbalancedChen.Certificates.PairedV2StripCertificate504RightB

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip504_checked_right : ∀ j : Fin 92,
    (makeCertificate (⟨(⟨178, by decide⟩ : Fin 186), Fin.cast strip504_row_count.symm (Fin.natAdd 91 j)⟩ : Row) (approximation (⟨(⟨178, by decide⟩ : Fin 186), Fin.cast strip504_row_count.symm (Fin.natAdd 91 j)⟩ : Row))).check = true := by
  exact StripAssembly.forallFinAdd (a := 46) (b := 46)
    (fun j => (makeCertificate (⟨(⟨178, by decide⟩ : Fin 186), Fin.cast strip504_row_count.symm (Fin.natAdd 91 j)⟩ : Row) (approximation (⟨(⟨178, by decide⟩ : Fin 186), Fin.cast strip504_row_count.symm (Fin.natAdd 91 j)⟩ : Row))).check = true)
    strip504_checked_right_a strip504_checked_right_b

end ImbalancedChen.Certificates.PairedV2.FullMask
