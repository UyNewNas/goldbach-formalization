import ImbalancedChen.Certificates.PairedV2StripFiniteAssembly
import ImbalancedChen.Certificates.PairedV2StripCertificate488RightA
import ImbalancedChen.Certificates.PairedV2StripCertificate488RightB

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip488_checked_right : ∀ j : Fin 83,
    (makeCertificate (⟨(⟨162, by decide⟩ : Fin 186), Fin.cast strip488_row_count.symm (Fin.natAdd 83 j)⟩ : Row) (approximation (⟨(⟨162, by decide⟩ : Fin 186), Fin.cast strip488_row_count.symm (Fin.natAdd 83 j)⟩ : Row))).check = true := by
  exact StripAssembly.forallFinAdd (a := 41) (b := 42)
    (fun j => (makeCertificate (⟨(⟨162, by decide⟩ : Fin 186), Fin.cast strip488_row_count.symm (Fin.natAdd 83 j)⟩ : Row) (approximation (⟨(⟨162, by decide⟩ : Fin 186), Fin.cast strip488_row_count.symm (Fin.natAdd 83 j)⟩ : Row))).check = true)
    strip488_checked_right_a strip488_checked_right_b

end ImbalancedChen.Certificates.PairedV2.FullMask
