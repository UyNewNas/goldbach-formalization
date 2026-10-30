import ImbalancedChen.Certificates.PairedV2StripCertificate459Bounds

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip459_checked_right : ∀ j : Fin 68,
    (makeCertificate (⟨(⟨133, by decide⟩ : Fin 186), Fin.cast strip459_row_count.symm (Fin.natAdd 68 j)⟩ : Row) (approximation (⟨(⟨133, by decide⟩ : Fin 186), Fin.cast strip459_row_count.symm (Fin.natAdd 68 j)⟩ : Row))).check = true := by
  decide +kernel

end ImbalancedChen.Certificates.PairedV2.FullMask
