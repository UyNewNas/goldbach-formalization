import ImbalancedChen.Certificates.PairedV2StripCertificate487Bounds

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip487_checked_right_a : ∀ j : Fin 41,
    (makeCertificate (⟨(⟨161, by decide⟩ : Fin 186), Fin.cast strip487_row_count.symm (Fin.natAdd 82 (Fin.castAdd 42 j))⟩ : Row) (approximation (⟨(⟨161, by decide⟩ : Fin 186), Fin.cast strip487_row_count.symm (Fin.natAdd 82 (Fin.castAdd 42 j))⟩ : Row))).check = true := by
  decide +kernel

end ImbalancedChen.Certificates.PairedV2.FullMask
