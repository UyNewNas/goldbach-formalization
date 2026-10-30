import ImbalancedChen.Certificates.PairedV2StripCertificatesAssemblyCore

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip474_firstU : firstU (⟨148, by decide⟩ : Fin 186) = 360 := by
  rfl

theorem strip474_row_count : 512 - firstU (⟨148, by decide⟩ : Fin 186) = 152 := by
  rw [strip474_firstU]

end ImbalancedChen.Certificates.PairedV2.FullMask
