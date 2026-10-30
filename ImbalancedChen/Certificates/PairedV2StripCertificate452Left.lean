import ImbalancedChen.Certificates.PairedV2StripCertificate452Bounds

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip452_checked_left : ∀ j : Fin 64,
    (makeCertificate (⟨(⟨126, by decide⟩ : Fin 186), Fin.cast strip452_row_count.symm (Fin.castAdd 65 j)⟩ : Row) (approximation (⟨(⟨126, by decide⟩ : Fin 186), Fin.cast strip452_row_count.symm (Fin.castAdd 65 j)⟩ : Row))).check = true := by
  decide +kernel

end ImbalancedChen.Certificates.PairedV2.FullMask
