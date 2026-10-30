import ImbalancedChen.Certificates.PairedV2StripCertificate423Bounds

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip423_checked_left : ∀ j : Fin 49,
    (makeCertificate (⟨(⟨97, by decide⟩ : Fin 186), Fin.cast strip423_row_count.symm (Fin.castAdd 49 j)⟩ : Row) (approximation (⟨(⟨97, by decide⟩ : Fin 186), Fin.cast strip423_row_count.symm (Fin.castAdd 49 j)⟩ : Row))).check = true := by
  decide +kernel

end ImbalancedChen.Certificates.PairedV2.FullMask
