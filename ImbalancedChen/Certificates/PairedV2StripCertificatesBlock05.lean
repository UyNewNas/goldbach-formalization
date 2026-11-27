import ImbalancedChen.Certificates.PairedV2StripCertificatesAssemblyCore

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip406_checked : ∀ j : Fin (512 - firstU (⟨80, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨80, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨80, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip407_checked : ∀ j : Fin (512 - firstU (⟨81, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨81, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨81, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip408_checked : ∀ j : Fin (512 - firstU (⟨82, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨82, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨82, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip409_checked : ∀ j : Fin (512 - firstU (⟨83, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨83, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨83, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip410_checked : ∀ j : Fin (512 - firstU (⟨84, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨84, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨84, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip411_checked : ∀ j : Fin (512 - firstU (⟨85, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨85, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨85, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip412_checked : ∀ j : Fin (512 - firstU (⟨86, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨86, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨86, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip413_checked : ∀ j : Fin (512 - firstU (⟨87, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨87, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨87, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip414_checked : ∀ j : Fin (512 - firstU (⟨88, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨88, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨88, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip415_checked : ∀ j : Fin (512 - firstU (⟨89, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨89, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨89, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip416_checked : ∀ j : Fin (512 - firstU (⟨90, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨90, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨90, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip417_checked : ∀ j : Fin (512 - firstU (⟨91, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨91, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨91, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip418_checked : ∀ j : Fin (512 - firstU (⟨92, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨92, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨92, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip419_checked : ∀ j : Fin (512 - firstU (⟨93, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨93, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨93, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip420_checked : ∀ j : Fin (512 - firstU (⟨94, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨94, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨94, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip421_checked : ∀ j : Fin (512 - firstU (⟨95, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨95, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨95, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

/-- Bounded composition of the original strip checks, with no new check assumption. -/
theorem stripBlock05_checked (k : Fin 16) :
    StripAssembly.StripChecked (StripAssembly.indexBlock05 k) := by
  fin_cases k
  · exact strip406_checked
  · exact strip407_checked
  · exact strip408_checked
  · exact strip409_checked
  · exact strip410_checked
  · exact strip411_checked
  · exact strip412_checked
  · exact strip413_checked
  · exact strip414_checked
  · exact strip415_checked
  · exact strip416_checked
  · exact strip417_checked
  · exact strip418_checked
  · exact strip419_checked
  · exact strip420_checked
  · exact strip421_checked

end ImbalancedChen.Certificates.PairedV2.FullMask
