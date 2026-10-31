import ImbalancedChen.Certificates.PairedV2StripCertificate481Bounds

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip481_checked_right_b : ∀ j : Fin 40,
    (makeCertificate (⟨(⟨155, by decide⟩ : Fin 186), Fin.cast strip481_row_count.symm (Fin.natAdd 79 (Fin.natAdd 40 j))⟩ : Row) (approximation (⟨(⟨155, by decide⟩ : Fin 186), Fin.cast strip481_row_count.symm (Fin.natAdd 79 (Fin.natAdd 40 j))⟩ : Row))).check = true := by
  decide +kernel

end ImbalancedChen.Certificates.PairedV2.FullMask
