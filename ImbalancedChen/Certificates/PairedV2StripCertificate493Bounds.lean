import ImbalancedChen.Certificates.PairedV2StripCertificatesAssemblyCore

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip493_firstU : firstU (⟨167, by decide⟩ : Fin 186) = 340 := by
  rfl

theorem strip493_row_count : 512 - firstU (⟨167, by decide⟩ : Fin 186) = 172 := by
  rw [strip493_firstU]

end ImbalancedChen.Certificates.PairedV2.FullMask
