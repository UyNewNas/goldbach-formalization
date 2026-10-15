import ImbalancedChen.Certificates.PairedV2StripCertificatesAssemblyCore

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip470_checked : ∀ j : Fin (512 - firstU (⟨144, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨144, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨144, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip471_checked : ∀ j : Fin (512 - firstU (⟨145, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨145, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨145, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip472_checked : ∀ j : Fin (512 - firstU (⟨146, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨146, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨146, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip473_checked : ∀ j : Fin (512 - firstU (⟨147, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨147, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨147, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip474_checked : ∀ j : Fin (512 - firstU (⟨148, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨148, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨148, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip475_checked : ∀ j : Fin (512 - firstU (⟨149, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨149, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨149, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip476_checked : ∀ j : Fin (512 - firstU (⟨150, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨150, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨150, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip477_checked : ∀ j : Fin (512 - firstU (⟨151, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨151, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨151, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip478_checked : ∀ j : Fin (512 - firstU (⟨152, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨152, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨152, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip479_checked : ∀ j : Fin (512 - firstU (⟨153, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨153, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨153, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip480_checked : ∀ j : Fin (512 - firstU (⟨154, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨154, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨154, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip481_checked : ∀ j : Fin (512 - firstU (⟨155, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨155, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨155, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip482_checked : ∀ j : Fin (512 - firstU (⟨156, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨156, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨156, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip483_checked : ∀ j : Fin (512 - firstU (⟨157, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨157, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨157, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip484_checked : ∀ j : Fin (512 - firstU (⟨158, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨158, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨158, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip485_checked : ∀ j : Fin (512 - firstU (⟨159, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨159, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨159, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

/-- Bounded composition of the original strip checks, with no new check assumption. -/
theorem stripBlock09_checked (k : Fin 16) :
    StripAssembly.StripChecked (StripAssembly.indexBlock09 k) := by
  fin_cases k
  · exact strip470_checked
  · exact strip471_checked
  · exact strip472_checked
  · exact strip473_checked
  · exact strip474_checked
  · exact strip475_checked
  · exact strip476_checked
  · exact strip477_checked
  · exact strip478_checked
  · exact strip479_checked
  · exact strip480_checked
  · exact strip481_checked
  · exact strip482_checked
  · exact strip483_checked
  · exact strip484_checked
  · exact strip485_checked

end ImbalancedChen.Certificates.PairedV2.FullMask
