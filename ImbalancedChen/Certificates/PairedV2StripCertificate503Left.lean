import ImbalancedChen.Certificates.PairedV2StripCertificate503Bounds

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip503_checked_left : ∀ j : Fin 91,
    (makeCertificate (⟨(⟨177, by decide⟩ : Fin 186), Fin.cast strip503_row_count.symm (Fin.castAdd 91 j)⟩ : Row) (approximation (⟨(⟨177, by decide⟩ : Fin 186), Fin.cast strip503_row_count.symm (Fin.castAdd 91 j)⟩ : Row))).check = true := by
  decide +kernel

end ImbalancedChen.Certificates.PairedV2.FullMask
