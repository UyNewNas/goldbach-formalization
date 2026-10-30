import ImbalancedChen.Certificates.PairedV2StripCertificatesAssemblyCore

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip458_firstU : firstU (⟨132, by decide⟩ : Fin 186) = 377 := by
  rfl

theorem strip458_row_count : 512 - firstU (⟨132, by decide⟩ : Fin 186) = 135 := by
  rw [strip458_firstU]

end ImbalancedChen.Certificates.PairedV2.FullMask
