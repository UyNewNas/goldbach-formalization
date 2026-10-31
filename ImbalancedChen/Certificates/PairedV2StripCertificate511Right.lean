import ImbalancedChen.Certificates.PairedV2StripFiniteAssembly
import ImbalancedChen.Certificates.PairedV2StripCertificate511RightA
import ImbalancedChen.Certificates.PairedV2StripCertificate511RightB

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip511_checked_right : ∀ j : Fin 96,
    (makeCertificate (⟨(⟨185, by decide⟩ : Fin 186), Fin.cast strip511_row_count.symm (Fin.natAdd 95 j)⟩ : Row) (approximation (⟨(⟨185, by decide⟩ : Fin 186), Fin.cast strip511_row_count.symm (Fin.natAdd 95 j)⟩ : Row))).check = true := by
  exact StripAssembly.forallFinAdd (a := 48) (b := 48)
    (fun j => (makeCertificate (⟨(⟨185, by decide⟩ : Fin 186), Fin.cast strip511_row_count.symm (Fin.natAdd 95 j)⟩ : Row) (approximation (⟨(⟨185, by decide⟩ : Fin 186), Fin.cast strip511_row_count.symm (Fin.natAdd 95 j)⟩ : Row))).check = true)
    strip511_checked_right_a strip511_checked_right_b

end ImbalancedChen.Certificates.PairedV2.FullMask
