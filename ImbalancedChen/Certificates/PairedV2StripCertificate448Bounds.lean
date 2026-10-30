import ImbalancedChen.Certificates.PairedV2StripCertificatesAssemblyCore

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip448_firstU : firstU (⟨122, by decide⟩ : Fin 186) = 388 := by
  rfl

theorem strip448_row_count : 512 - firstU (⟨122, by decide⟩ : Fin 186) = 124 := by
  rw [strip448_firstU]

end ImbalancedChen.Certificates.PairedV2.FullMask
