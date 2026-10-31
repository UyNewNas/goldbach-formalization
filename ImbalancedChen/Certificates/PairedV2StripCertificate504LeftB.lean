import ImbalancedChen.Certificates.PairedV2StripCertificate504Bounds

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip504_checked_left_b : ∀ j : Fin 46,
    (makeCertificate (⟨(⟨178, by decide⟩ : Fin 186), Fin.cast strip504_row_count.symm (Fin.castAdd 92 (Fin.natAdd 45 j))⟩ : Row) (approximation (⟨(⟨178, by decide⟩ : Fin 186), Fin.cast strip504_row_count.symm (Fin.castAdd 92 (Fin.natAdd 45 j))⟩ : Row))).check = true := by
  decide +kernel

end ImbalancedChen.Certificates.PairedV2.FullMask
