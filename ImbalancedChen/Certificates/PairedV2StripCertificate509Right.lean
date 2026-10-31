import ImbalancedChen.Certificates.PairedV2StripFiniteAssembly
import ImbalancedChen.Certificates.PairedV2StripCertificate509RightA
import ImbalancedChen.Certificates.PairedV2StripCertificate509RightB

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip509_checked_right : ∀ j : Fin 95,
    (makeCertificate (⟨(⟨183, by decide⟩ : Fin 186), Fin.cast strip509_row_count.symm (Fin.natAdd 94 j)⟩ : Row) (approximation (⟨(⟨183, by decide⟩ : Fin 186), Fin.cast strip509_row_count.symm (Fin.natAdd 94 j)⟩ : Row))).check = true := by
  exact StripAssembly.forallFinAdd (a := 47) (b := 48)
    (fun j => (makeCertificate (⟨(⟨183, by decide⟩ : Fin 186), Fin.cast strip509_row_count.symm (Fin.natAdd 94 j)⟩ : Row) (approximation (⟨(⟨183, by decide⟩ : Fin 186), Fin.cast strip509_row_count.symm (Fin.natAdd 94 j)⟩ : Row))).check = true)
    strip509_checked_right_a strip509_checked_right_b

end ImbalancedChen.Certificates.PairedV2.FullMask
