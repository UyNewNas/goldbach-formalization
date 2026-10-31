import ImbalancedChen.Certificates.PairedV2StripCertificate500Bounds

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip500_checked_left_a : ∀ j : Fin 44,
    (makeCertificate (⟨(⟨174, by decide⟩ : Fin 186), Fin.cast strip500_row_count.symm (Fin.castAdd 90 (Fin.castAdd 45 j))⟩ : Row) (approximation (⟨(⟨174, by decide⟩ : Fin 186), Fin.cast strip500_row_count.symm (Fin.castAdd 90 (Fin.castAdd 45 j))⟩ : Row))).check = true := by
  decide +kernel

end ImbalancedChen.Certificates.PairedV2.FullMask
