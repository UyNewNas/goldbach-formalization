import ImbalancedChen.Certificates.PairedV2StripCertificate505Bounds

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip505_checked_left_b : ∀ j : Fin 46,
    (makeCertificate (⟨(⟨179, by decide⟩ : Fin 186), Fin.cast strip505_row_count.symm (Fin.castAdd 92 (Fin.natAdd 46 j))⟩ : Row) (approximation (⟨(⟨179, by decide⟩ : Fin 186), Fin.cast strip505_row_count.symm (Fin.castAdd 92 (Fin.natAdd 46 j))⟩ : Row))).check = true := by
  decide +kernel

end ImbalancedChen.Certificates.PairedV2.FullMask
