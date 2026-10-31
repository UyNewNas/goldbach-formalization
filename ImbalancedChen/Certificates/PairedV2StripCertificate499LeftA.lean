import ImbalancedChen.Certificates.PairedV2StripCertificate499Bounds

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip499_checked_left_a : ∀ j : Fin 44,
    (makeCertificate (⟨(⟨173, by decide⟩ : Fin 186), Fin.cast strip499_row_count.symm (Fin.castAdd 89 (Fin.castAdd 45 j))⟩ : Row) (approximation (⟨(⟨173, by decide⟩ : Fin 186), Fin.cast strip499_row_count.symm (Fin.castAdd 89 (Fin.castAdd 45 j))⟩ : Row))).check = true := by
  decide +kernel

end ImbalancedChen.Certificates.PairedV2.FullMask
