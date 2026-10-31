import ImbalancedChen.Certificates.PairedV2StripCertificate488Bounds

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip488_checked_right_a : ∀ j : Fin 41,
    (makeCertificate (⟨(⟨162, by decide⟩ : Fin 186), Fin.cast strip488_row_count.symm (Fin.natAdd 83 (Fin.castAdd 42 j))⟩ : Row) (approximation (⟨(⟨162, by decide⟩ : Fin 186), Fin.cast strip488_row_count.symm (Fin.natAdd 83 (Fin.castAdd 42 j))⟩ : Row))).check = true := by
  decide +kernel

end ImbalancedChen.Certificates.PairedV2.FullMask
