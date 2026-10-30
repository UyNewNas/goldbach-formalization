import ImbalancedChen.Certificates.PairedV2StripCertificatesAssemblyCore

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip498_firstU : firstU (⟨172, by decide⟩ : Fin 186) = 335 := by
  rfl

theorem strip498_row_count : 512 - firstU (⟨172, by decide⟩ : Fin 186) = 177 := by
  rw [strip498_firstU]

end ImbalancedChen.Certificates.PairedV2.FullMask
