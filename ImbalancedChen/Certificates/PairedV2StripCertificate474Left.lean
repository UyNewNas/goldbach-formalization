import ImbalancedChen.Certificates.PairedV2StripCertificate474Bounds

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip474_checked_left : ∀ j : Fin 76,
    (makeCertificate (⟨(⟨148, by decide⟩ : Fin 186), Fin.cast strip474_row_count.symm (Fin.castAdd 76 j)⟩ : Row) (approximation (⟨(⟨148, by decide⟩ : Fin 186), Fin.cast strip474_row_count.symm (Fin.castAdd 76 j)⟩ : Row))).check = true := by
  decide +kernel

end ImbalancedChen.Certificates.PairedV2.FullMask
