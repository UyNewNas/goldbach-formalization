import ImbalancedChen.Certificates.PairedV2StripCertificate497Bounds

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip497_checked_right_b : ∀ j : Fin 44,
    (makeCertificate (⟨(⟨171, by decide⟩ : Fin 186), Fin.cast strip497_row_count.symm (Fin.natAdd 88 (Fin.natAdd 44 j))⟩ : Row) (approximation (⟨(⟨171, by decide⟩ : Fin 186), Fin.cast strip497_row_count.symm (Fin.natAdd 88 (Fin.natAdd 44 j))⟩ : Row))).check = true := by
  decide +kernel

end ImbalancedChen.Certificates.PairedV2.FullMask
