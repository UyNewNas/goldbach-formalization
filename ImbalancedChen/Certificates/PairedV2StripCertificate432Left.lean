import ImbalancedChen.Certificates.PairedV2StripCertificate432Bounds

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip432_checked_left : ∀ j : Fin 54,
    (makeCertificate (⟨(⟨106, by decide⟩ : Fin 186), Fin.cast strip432_row_count.symm (Fin.castAdd 54 j)⟩ : Row) (approximation (⟨(⟨106, by decide⟩ : Fin 186), Fin.cast strip432_row_count.symm (Fin.castAdd 54 j)⟩ : Row))).check = true := by
  decide +kernel

end ImbalancedChen.Certificates.PairedV2.FullMask
