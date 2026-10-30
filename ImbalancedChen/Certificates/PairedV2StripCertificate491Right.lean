import ImbalancedChen.Certificates.PairedV2StripFiniteAssembly
import ImbalancedChen.Certificates.PairedV2StripCertificate491RightA
import ImbalancedChen.Certificates.PairedV2StripCertificate491RightB

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip491_checked_right : ∀ j : Fin 85,
    (makeCertificate (⟨(⟨165, by decide⟩ : Fin 186), Fin.cast strip491_row_count.symm (Fin.natAdd 85 j)⟩ : Row) (approximation (⟨(⟨165, by decide⟩ : Fin 186), Fin.cast strip491_row_count.symm (Fin.natAdd 85 j)⟩ : Row))).check = true := by
  exact StripAssembly.forallFinAdd (a := 42) (b := 43)
    (fun j => (makeCertificate (⟨(⟨165, by decide⟩ : Fin 186), Fin.cast strip491_row_count.symm (Fin.natAdd 85 j)⟩ : Row) (approximation (⟨(⟨165, by decide⟩ : Fin 186), Fin.cast strip491_row_count.symm (Fin.natAdd 85 j)⟩ : Row))).check = true)
    strip491_checked_right_a strip491_checked_right_b

end ImbalancedChen.Certificates.PairedV2.FullMask
