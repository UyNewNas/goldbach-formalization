import ImbalancedChen.Certificates.PairedV2StripCertificate470Bounds

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip470_checked_left : ∀ j : Fin 73,
    (makeCertificate (⟨(⟨144, by decide⟩ : Fin 186), Fin.cast strip470_row_count.symm (Fin.castAdd 74 j)⟩ : Row) (approximation (⟨(⟨144, by decide⟩ : Fin 186), Fin.cast strip470_row_count.symm (Fin.castAdd 74 j)⟩ : Row))).check = true := by
  decide +kernel

end ImbalancedChen.Certificates.PairedV2.FullMask
