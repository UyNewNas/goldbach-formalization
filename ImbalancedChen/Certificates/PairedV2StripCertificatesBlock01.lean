import ImbalancedChen.Certificates.PairedV2StripCertificatesAssemblyCore

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip342_checked : ∀ j : Fin (512 - firstU (⟨16, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨16, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨16, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip343_checked : ∀ j : Fin (512 - firstU (⟨17, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨17, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨17, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip344_checked : ∀ j : Fin (512 - firstU (⟨18, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨18, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨18, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip345_checked : ∀ j : Fin (512 - firstU (⟨19, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨19, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨19, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip346_checked : ∀ j : Fin (512 - firstU (⟨20, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨20, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨20, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip347_checked : ∀ j : Fin (512 - firstU (⟨21, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨21, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨21, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip348_checked : ∀ j : Fin (512 - firstU (⟨22, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨22, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨22, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip349_checked : ∀ j : Fin (512 - firstU (⟨23, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨23, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨23, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip350_checked : ∀ j : Fin (512 - firstU (⟨24, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨24, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨24, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip351_checked : ∀ j : Fin (512 - firstU (⟨25, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨25, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨25, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip352_checked : ∀ j : Fin (512 - firstU (⟨26, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨26, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨26, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip353_checked : ∀ j : Fin (512 - firstU (⟨27, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨27, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨27, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip354_checked : ∀ j : Fin (512 - firstU (⟨28, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨28, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨28, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip355_checked : ∀ j : Fin (512 - firstU (⟨29, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨29, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨29, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip356_checked : ∀ j : Fin (512 - firstU (⟨30, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨30, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨30, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip357_checked : ∀ j : Fin (512 - firstU (⟨31, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨31, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨31, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

/-- Bounded composition of the original strip checks, with no new check assumption. -/
theorem stripBlock01_checked (k : Fin 16) :
    StripAssembly.StripChecked (StripAssembly.indexBlock01 k) := by
  fin_cases k
  · exact strip342_checked
  · exact strip343_checked
  · exact strip344_checked
  · exact strip345_checked
  · exact strip346_checked
  · exact strip347_checked
  · exact strip348_checked
  · exact strip349_checked
  · exact strip350_checked
  · exact strip351_checked
  · exact strip352_checked
  · exact strip353_checked
  · exact strip354_checked
  · exact strip355_checked
  · exact strip356_checked
  · exact strip357_checked

end ImbalancedChen.Certificates.PairedV2.FullMask
