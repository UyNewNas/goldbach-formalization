import ImbalancedChen.Certificates.PairedV2StripCertificate509Bounds

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip509_checked_right_b : ∀ j : Fin 48,
    (makeCertificate (⟨(⟨183, by decide⟩ : Fin 186), Fin.cast strip509_row_count.symm (Fin.natAdd 94 (Fin.natAdd 47 j))⟩ : Row) (approximation (⟨(⟨183, by decide⟩ : Fin 186), Fin.cast strip509_row_count.symm (Fin.natAdd 94 (Fin.natAdd 47 j))⟩ : Row))).check = true := by
  decide +kernel

end ImbalancedChen.Certificates.PairedV2.FullMask
