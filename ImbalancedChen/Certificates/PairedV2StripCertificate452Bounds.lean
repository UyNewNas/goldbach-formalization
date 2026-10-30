import ImbalancedChen.Certificates.PairedV2StripCertificatesAssemblyCore

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip452_firstU : firstU (⟨126, by decide⟩ : Fin 186) = 383 := by
  rfl

theorem strip452_row_count : 512 - firstU (⟨126, by decide⟩ : Fin 186) = 129 := by
  rw [strip452_firstU]

end ImbalancedChen.Certificates.PairedV2.FullMask
