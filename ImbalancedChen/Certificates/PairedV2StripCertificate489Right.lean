import ImbalancedChen.Certificates.PairedV2StripFiniteAssembly
import ImbalancedChen.Certificates.PairedV2StripCertificate489RightA
import ImbalancedChen.Certificates.PairedV2StripCertificate489RightB

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip489_checked_right : ∀ j : Fin 84,
    (makeCertificate (⟨(⟨163, by decide⟩ : Fin 186), Fin.cast strip489_row_count.symm (Fin.natAdd 84 j)⟩ : Row) (approximation (⟨(⟨163, by decide⟩ : Fin 186), Fin.cast strip489_row_count.symm (Fin.natAdd 84 j)⟩ : Row))).check = true := by
  exact StripAssembly.forallFinAdd (a := 42) (b := 42)
    (fun j => (makeCertificate (⟨(⟨163, by decide⟩ : Fin 186), Fin.cast strip489_row_count.symm (Fin.natAdd 84 j)⟩ : Row) (approximation (⟨(⟨163, by decide⟩ : Fin 186), Fin.cast strip489_row_count.symm (Fin.natAdd 84 j)⟩ : Row))).check = true)
    strip489_checked_right_a strip489_checked_right_b

end ImbalancedChen.Certificates.PairedV2.FullMask
