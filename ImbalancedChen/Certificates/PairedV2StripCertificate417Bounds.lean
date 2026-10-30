import ImbalancedChen.Certificates.PairedV2StripCertificatesAssemblyCore

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip417_firstU : firstU (⟨91, by decide⟩ : Fin 186) = 420 := by
  rfl

theorem strip417_row_count : 512 - firstU (⟨91, by decide⟩ : Fin 186) = 92 := by
  rw [strip417_firstU]

end ImbalancedChen.Certificates.PairedV2.FullMask
