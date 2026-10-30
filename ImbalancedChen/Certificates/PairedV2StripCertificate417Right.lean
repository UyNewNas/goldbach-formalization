import ImbalancedChen.Certificates.PairedV2StripCertificate417Bounds

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip417_checked_right : ∀ j : Fin 46,
    (makeCertificate (⟨(⟨91, by decide⟩ : Fin 186), Fin.cast strip417_row_count.symm (Fin.natAdd 46 j)⟩ : Row) (approximation (⟨(⟨91, by decide⟩ : Fin 186), Fin.cast strip417_row_count.symm (Fin.natAdd 46 j)⟩ : Row))).check = true := by
  decide +kernel

end ImbalancedChen.Certificates.PairedV2.FullMask
