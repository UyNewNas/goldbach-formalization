import ImbalancedChen.Certificates.PairedV2StripCertificatesAssemblyCore

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip486_checked : ∀ j : Fin (512 - firstU (⟨160, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨160, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨160, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip487_checked : ∀ j : Fin (512 - firstU (⟨161, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨161, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨161, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip488_checked : ∀ j : Fin (512 - firstU (⟨162, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨162, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨162, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip489_checked : ∀ j : Fin (512 - firstU (⟨163, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨163, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨163, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip490_checked : ∀ j : Fin (512 - firstU (⟨164, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨164, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨164, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip491_checked : ∀ j : Fin (512 - firstU (⟨165, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨165, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨165, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip492_checked : ∀ j : Fin (512 - firstU (⟨166, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨166, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨166, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip493_checked : ∀ j : Fin (512 - firstU (⟨167, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨167, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨167, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip494_checked : ∀ j : Fin (512 - firstU (⟨168, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨168, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨168, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip495_checked : ∀ j : Fin (512 - firstU (⟨169, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨169, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨169, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip496_checked : ∀ j : Fin (512 - firstU (⟨170, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨170, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨170, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip497_checked : ∀ j : Fin (512 - firstU (⟨171, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨171, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨171, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip498_checked : ∀ j : Fin (512 - firstU (⟨172, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨172, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨172, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip499_checked : ∀ j : Fin (512 - firstU (⟨173, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨173, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨173, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip500_checked : ∀ j : Fin (512 - firstU (⟨174, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨174, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨174, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip501_checked : ∀ j : Fin (512 - firstU (⟨175, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨175, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨175, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

/-- Bounded composition of the original strip checks, with no new check assumption. -/
theorem stripBlock10_checked (k : Fin 16) :
    StripAssembly.StripChecked (StripAssembly.indexBlock10 k) := by
  fin_cases k
  · exact strip486_checked
  · exact strip487_checked
  · exact strip488_checked
  · exact strip489_checked
  · exact strip490_checked
  · exact strip491_checked
  · exact strip492_checked
  · exact strip493_checked
  · exact strip494_checked
  · exact strip495_checked
  · exact strip496_checked
  · exact strip497_checked
  · exact strip498_checked
  · exact strip499_checked
  · exact strip500_checked
  · exact strip501_checked

end ImbalancedChen.Certificates.PairedV2.FullMask
