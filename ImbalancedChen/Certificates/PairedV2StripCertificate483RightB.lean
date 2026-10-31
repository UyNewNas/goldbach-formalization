import ImbalancedChen.Certificates.PairedV2StripCertificate483Bounds

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip483_checked_right_b : ∀ j : Fin 41,
    (makeCertificate (⟨(⟨157, by decide⟩ : Fin 186), Fin.cast strip483_row_count.symm (Fin.natAdd 80 (Fin.natAdd 40 j))⟩ : Row) (approximation (⟨(⟨157, by decide⟩ : Fin 186), Fin.cast strip483_row_count.symm (Fin.natAdd 80 (Fin.natAdd 40 j))⟩ : Row))).check = true := by
  decide +kernel

end ImbalancedChen.Certificates.PairedV2.FullMask
