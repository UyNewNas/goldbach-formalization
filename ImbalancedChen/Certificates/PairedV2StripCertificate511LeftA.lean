import ImbalancedChen.Certificates.PairedV2StripCertificate511Bounds

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip511_checked_left_a : ∀ j : Fin 47,
    (makeCertificate (⟨(⟨185, by decide⟩ : Fin 186), Fin.cast strip511_row_count.symm (Fin.castAdd 96 (Fin.castAdd 48 j))⟩ : Row) (approximation (⟨(⟨185, by decide⟩ : Fin 186), Fin.cast strip511_row_count.symm (Fin.castAdd 96 (Fin.castAdd 48 j))⟩ : Row))).check = true := by
  decide +kernel

end ImbalancedChen.Certificates.PairedV2.FullMask
