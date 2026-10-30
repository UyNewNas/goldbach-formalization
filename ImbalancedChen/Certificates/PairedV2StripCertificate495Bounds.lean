import ImbalancedChen.Certificates.PairedV2StripCertificatesAssemblyCore

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip495_firstU : firstU (⟨169, by decide⟩ : Fin 186) = 338 := by
  rfl

theorem strip495_row_count : 512 - firstU (⟨169, by decide⟩ : Fin 186) = 174 := by
  rw [strip495_firstU]

end ImbalancedChen.Certificates.PairedV2.FullMask
