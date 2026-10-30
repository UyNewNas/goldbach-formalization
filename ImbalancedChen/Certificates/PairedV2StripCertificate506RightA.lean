import ImbalancedChen.Certificates.PairedV2StripCertificate506Bounds

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip506_checked_right_a : ∀ j : Fin 46,
    (makeCertificate (⟨(⟨180, by decide⟩ : Fin 186), Fin.cast strip506_row_count.symm (Fin.natAdd 92 (Fin.castAdd 47 j))⟩ : Row) (approximation (⟨(⟨180, by decide⟩ : Fin 186), Fin.cast strip506_row_count.symm (Fin.natAdd 92 (Fin.castAdd 47 j))⟩ : Row))).check = true := by
  decide +kernel

end ImbalancedChen.Certificates.PairedV2.FullMask
