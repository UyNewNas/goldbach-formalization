import ImbalancedChen.Certificates.PairedV2StripCertificate458Bounds

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip458_checked_left : ∀ j : Fin 67,
    (makeCertificate (⟨(⟨132, by decide⟩ : Fin 186), Fin.cast strip458_row_count.symm (Fin.castAdd 68 j)⟩ : Row) (approximation (⟨(⟨132, by decide⟩ : Fin 186), Fin.cast strip458_row_count.symm (Fin.castAdd 68 j)⟩ : Row))).check = true := by
  decide +kernel

end ImbalancedChen.Certificates.PairedV2.FullMask
