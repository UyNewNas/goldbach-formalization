import ImbalancedChen.Certificates.PairedV2StripCertificate461Bounds

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip461_checked_left : ∀ j : Fin 69,
    (makeCertificate (⟨(⟨135, by decide⟩ : Fin 186), Fin.cast strip461_row_count.symm (Fin.castAdd 69 j)⟩ : Row) (approximation (⟨(⟨135, by decide⟩ : Fin 186), Fin.cast strip461_row_count.symm (Fin.castAdd 69 j)⟩ : Row))).check = true := by
  decide +kernel

end ImbalancedChen.Certificates.PairedV2.FullMask
