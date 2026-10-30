import ImbalancedChen.Certificates.PairedV2StripCertificate493Bounds

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip493_checked_left : ∀ j : Fin 86,
    (makeCertificate (⟨(⟨167, by decide⟩ : Fin 186), Fin.cast strip493_row_count.symm (Fin.castAdd 86 j)⟩ : Row) (approximation (⟨(⟨167, by decide⟩ : Fin 186), Fin.cast strip493_row_count.symm (Fin.castAdd 86 j)⟩ : Row))).check = true := by
  decide +kernel

end ImbalancedChen.Certificates.PairedV2.FullMask
