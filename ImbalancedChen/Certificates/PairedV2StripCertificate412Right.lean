import ImbalancedChen.Certificates.PairedV2StripCertificate412Bounds

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip412_checked_right : ∀ j : Fin 44,
    (makeCertificate (⟨(⟨86, by decide⟩ : Fin 186), Fin.cast strip412_row_count.symm (Fin.natAdd 43 j)⟩ : Row) (approximation (⟨(⟨86, by decide⟩ : Fin 186), Fin.cast strip412_row_count.symm (Fin.natAdd 43 j)⟩ : Row))).check = true := by
  decide +kernel

end ImbalancedChen.Certificates.PairedV2.FullMask
