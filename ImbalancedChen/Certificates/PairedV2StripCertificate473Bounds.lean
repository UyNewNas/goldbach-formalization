import ImbalancedChen.Certificates.PairedV2StripCertificatesAssemblyCore

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip473_firstU : firstU (⟨147, by decide⟩ : Fin 186) = 362 := by
  rfl

theorem strip473_row_count : 512 - firstU (⟨147, by decide⟩ : Fin 186) = 150 := by
  rw [strip473_firstU]

end ImbalancedChen.Certificates.PairedV2.FullMask
