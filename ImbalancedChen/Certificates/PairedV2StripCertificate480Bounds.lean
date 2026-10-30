import ImbalancedChen.Certificates.PairedV2StripCertificatesAssemblyCore

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip480_firstU : firstU (⟨154, by decide⟩ : Fin 186) = 354 := by
  rfl

theorem strip480_row_count : 512 - firstU (⟨154, by decide⟩ : Fin 186) = 158 := by
  rw [strip480_firstU]

end ImbalancedChen.Certificates.PairedV2.FullMask
