import ImbalancedChen.Certificates.PairedV2StripCertificate411Bounds

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip411_checked_left : ∀ j : Fin 43,
    (makeCertificate (⟨(⟨85, by decide⟩ : Fin 186), Fin.cast strip411_row_count.symm (Fin.castAdd 43 j)⟩ : Row) (approximation (⟨(⟨85, by decide⟩ : Fin 186), Fin.cast strip411_row_count.symm (Fin.castAdd 43 j)⟩ : Row))).check = true := by
  decide +kernel

end ImbalancedChen.Certificates.PairedV2.FullMask
