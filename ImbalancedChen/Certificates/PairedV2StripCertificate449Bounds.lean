import ImbalancedChen.Certificates.PairedV2StripCertificatesAssemblyCore

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip449_firstU : firstU (⟨123, by decide⟩ : Fin 186) = 387 := by
  rfl

theorem strip449_row_count : 512 - firstU (⟨123, by decide⟩ : Fin 186) = 125 := by
  rw [strip449_firstU]

end ImbalancedChen.Certificates.PairedV2.FullMask
