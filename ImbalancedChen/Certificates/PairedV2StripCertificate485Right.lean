import ImbalancedChen.Certificates.PairedV2StripCertificate485Bounds

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip485_checked_right : ∀ j : Fin 82,
    (makeCertificate (⟨(⟨159, by decide⟩ : Fin 186), Fin.cast strip485_row_count.symm (Fin.natAdd 81 j)⟩ : Row) (approximation (⟨(⟨159, by decide⟩ : Fin 186), Fin.cast strip485_row_count.symm (Fin.natAdd 81 j)⟩ : Row))).check = true := by
  decide +kernel

end ImbalancedChen.Certificates.PairedV2.FullMask
