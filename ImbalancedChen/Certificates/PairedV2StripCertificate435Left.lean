import ImbalancedChen.Certificates.PairedV2StripCertificate435Bounds

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip435_checked_left : ∀ j : Fin 55,
    (makeCertificate (⟨(⟨109, by decide⟩ : Fin 186), Fin.cast strip435_row_count.symm (Fin.castAdd 56 j)⟩ : Row) (approximation (⟨(⟨109, by decide⟩ : Fin 186), Fin.cast strip435_row_count.symm (Fin.castAdd 56 j)⟩ : Row))).check = true := by
  decide +kernel

end ImbalancedChen.Certificates.PairedV2.FullMask
