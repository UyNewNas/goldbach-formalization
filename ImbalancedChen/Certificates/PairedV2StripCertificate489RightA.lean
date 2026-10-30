import ImbalancedChen.Certificates.PairedV2StripCertificate489Bounds

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip489_checked_right_a : ∀ j : Fin 42,
    (makeCertificate (⟨(⟨163, by decide⟩ : Fin 186), Fin.cast strip489_row_count.symm (Fin.natAdd 84 (Fin.castAdd 42 j))⟩ : Row) (approximation (⟨(⟨163, by decide⟩ : Fin 186), Fin.cast strip489_row_count.symm (Fin.natAdd 84 (Fin.castAdd 42 j))⟩ : Row))).check = true := by
  decide +kernel

end ImbalancedChen.Certificates.PairedV2.FullMask
