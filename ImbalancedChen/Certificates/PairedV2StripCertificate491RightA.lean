import ImbalancedChen.Certificates.PairedV2StripCertificate491Bounds

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip491_checked_right_a : ∀ j : Fin 42,
    (makeCertificate (⟨(⟨165, by decide⟩ : Fin 186), Fin.cast strip491_row_count.symm (Fin.natAdd 85 (Fin.castAdd 43 j))⟩ : Row) (approximation (⟨(⟨165, by decide⟩ : Fin 186), Fin.cast strip491_row_count.symm (Fin.natAdd 85 (Fin.castAdd 43 j))⟩ : Row))).check = true := by
  decide +kernel

end ImbalancedChen.Certificates.PairedV2.FullMask
