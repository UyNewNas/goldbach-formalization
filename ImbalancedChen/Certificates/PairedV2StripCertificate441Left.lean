import ImbalancedChen.Certificates.PairedV2StripCertificate441Bounds

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip441_checked_left : ∀ j : Fin 58,
    (makeCertificate (⟨(⟨115, by decide⟩ : Fin 186), Fin.cast strip441_row_count.symm (Fin.castAdd 59 j)⟩ : Row) (approximation (⟨(⟨115, by decide⟩ : Fin 186), Fin.cast strip441_row_count.symm (Fin.castAdd 59 j)⟩ : Row))).check = true := by
  decide +kernel

end ImbalancedChen.Certificates.PairedV2.FullMask
