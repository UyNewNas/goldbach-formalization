import ImbalancedChen.Certificates.PairedV2StripCertificatesAssemblyCore

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip455_firstU : firstU (⟨129, by decide⟩ : Fin 186) = 380 := by
  rfl

theorem strip455_row_count : 512 - firstU (⟨129, by decide⟩ : Fin 186) = 132 := by
  rw [strip455_firstU]

end ImbalancedChen.Certificates.PairedV2.FullMask
