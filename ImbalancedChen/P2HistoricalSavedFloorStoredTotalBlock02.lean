import ImbalancedChen.P2HistoricalSavedFloorStoredTotalCore
import ImbalancedChen.P2HistoricalSavedFloorStripData422
import ImbalancedChen.P2HistoricalSavedFloorStripData423
import ImbalancedChen.P2HistoricalSavedFloorStripData424
import ImbalancedChen.P2HistoricalSavedFloorStripData425
import ImbalancedChen.P2HistoricalSavedFloorStripData426
import ImbalancedChen.P2HistoricalSavedFloorStripData427
import ImbalancedChen.P2HistoricalSavedFloorStripData428
import ImbalancedChen.P2HistoricalSavedFloorStripData429
import ImbalancedChen.P2HistoricalSavedFloorStripData430
import ImbalancedChen.P2HistoricalSavedFloorStripData431
import ImbalancedChen.P2HistoricalSavedFloorStripData432
import ImbalancedChen.P2HistoricalSavedFloorStripData433
import ImbalancedChen.P2HistoricalSavedFloorStripData434
import ImbalancedChen.P2HistoricalSavedFloorStripData435
import ImbalancedChen.P2HistoricalSavedFloorStripData436
import ImbalancedChen.P2HistoricalSavedFloorStripData437
import ImbalancedChen.P2HistoricalSavedFloorStripData438
import ImbalancedChen.P2HistoricalSavedFloorStripData439
import ImbalancedChen.P2HistoricalSavedFloorStripData440
import ImbalancedChen.P2HistoricalSavedFloorStripData441
import ImbalancedChen.P2HistoricalSavedFloorStripData442
import ImbalancedChen.P2HistoricalSavedFloorStripData443
import ImbalancedChen.P2HistoricalSavedFloorStripData444
import ImbalancedChen.P2HistoricalSavedFloorStripData445
import ImbalancedChen.P2HistoricalSavedFloorStripData446
import ImbalancedChen.P2HistoricalSavedFloorStripData447
import ImbalancedChen.P2HistoricalSavedFloorStripData448
import ImbalancedChen.P2HistoricalSavedFloorStripData449
import ImbalancedChen.P2HistoricalSavedFloorStripData450
import ImbalancedChen.P2HistoricalSavedFloorStripData451
import ImbalancedChen.P2HistoricalSavedFloorStripData452
import ImbalancedChen.P2HistoricalSavedFloorStripData453
import ImbalancedChen.P2HistoricalSavedFloorStripData454
import ImbalancedChen.P2HistoricalSavedFloorStripData455
import ImbalancedChen.P2HistoricalSavedFloorStripData456
import ImbalancedChen.P2HistoricalSavedFloorStripData457
import ImbalancedChen.P2HistoricalSavedFloorStripData458
import ImbalancedChen.P2HistoricalSavedFloorStripData459
import ImbalancedChen.P2HistoricalSavedFloorStripData460
import ImbalancedChen.P2HistoricalSavedFloorStripData461
import ImbalancedChen.P2HistoricalSavedFloorStripData462
import ImbalancedChen.P2HistoricalSavedFloorStripData463
import ImbalancedChen.P2HistoricalSavedFloorStripData464
import ImbalancedChen.P2HistoricalSavedFloorStripData465
import ImbalancedChen.P2HistoricalSavedFloorStripData466
import ImbalancedChen.P2HistoricalSavedFloorStripData467
import ImbalancedChen.P2HistoricalSavedFloorStripData468
import ImbalancedChen.P2HistoricalSavedFloorStripData469

namespace ImbalancedChen.P2HistoricalSavedFloorStoredTotal
open P2HistoricalSavedFloorRowsBinder
open Certificates.PairedV2 Certificates.PairedV2.FullMask
open scoped BigOperators
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip422_data_checked :
    (frozenSavedStrip422.map FrozenSavedRow.savedQ80).sum = (84771745342154755244 : ℤ) ∧
      frozenSavedStrip422.length = 512 - firstU (⟨96, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip422_sum :
    (∑ j : Fin (512 - firstU (⟨96, by decide⟩ : Fin 186)),
      (frozenSavedStrip422.getD j.val default).savedQ80) = (84771745342154755244 : ℤ) := by
  rw [← strip422_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip422_data_checked.1

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip423_data_checked :
    (frozenSavedStrip423.map FrozenSavedRow.savedQ80).sum = (83981723015803806364 : ℤ) ∧
      frozenSavedStrip423.length = 512 - firstU (⟨97, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip423_sum :
    (∑ j : Fin (512 - firstU (⟨97, by decide⟩ : Fin 186)),
      (frozenSavedStrip423.getD j.val default).savedQ80) = (83981723015803806364 : ℤ) := by
  rw [← strip423_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip423_data_checked.1

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip424_data_checked :
    (frozenSavedStrip424.map FrozenSavedRow.savedQ80).sum = (84991107686214959059 : ℤ) ∧
      frozenSavedStrip424.length = 512 - firstU (⟨98, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip424_sum :
    (∑ j : Fin (512 - firstU (⟨98, by decide⟩ : Fin 186)),
      (frozenSavedStrip424.getD j.val default).savedQ80) = (84991107686214959059 : ℤ) := by
  rw [← strip424_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip424_data_checked.1

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip425_data_checked :
    (frozenSavedStrip425.map FrozenSavedRow.savedQ80).sum = (84194192127536546198 : ℤ) ∧
      frozenSavedStrip425.length = 512 - firstU (⟨99, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip425_sum :
    (∑ j : Fin (512 - firstU (⟨99, by decide⟩ : Fin 186)),
      (frozenSavedStrip425.getD j.val default).savedQ80) = (84194192127536546198 : ℤ) := by
  rw [← strip425_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip425_data_checked.1

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip426_data_checked :
    (frozenSavedStrip426.map FrozenSavedRow.savedQ80).sum = (83698561772879733678 : ℤ) ∧
      frozenSavedStrip426.length = 512 - firstU (⟨100, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip426_sum :
    (∑ j : Fin (512 - firstU (⟨100, by decide⟩ : Fin 186)),
      (frozenSavedStrip426.getD j.val default).savedQ80) = (83698561772879733678 : ℤ) := by
  rw [← strip426_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip426_data_checked.1

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip427_data_checked :
    (frozenSavedStrip427.map FrozenSavedRow.savedQ80).sum = (82904486630298164318 : ℤ) ∧
      frozenSavedStrip427.length = 512 - firstU (⟨101, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip427_sum :
    (∑ j : Fin (512 - firstU (⟨101, by decide⟩ : Fin 186)),
      (frozenSavedStrip427.getD j.val default).savedQ80) = (82904486630298164318 : ℤ) := by
  rw [← strip427_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip427_data_checked.1

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip428_data_checked :
    (frozenSavedStrip428.map FrozenSavedRow.savedQ80).sum = (82407556237030346695 : ℤ) ∧
      frozenSavedStrip428.length = 512 - firstU (⟨102, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip428_sum :
    (∑ j : Fin (512 - firstU (⟨102, by decide⟩ : Fin 186)),
      (frozenSavedStrip428.getD j.val default).savedQ80) = (82407556237030346695 : ℤ) := by
  rw [← strip428_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip428_data_checked.1

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip429_data_checked :
    (frozenSavedStrip429.map FrozenSavedRow.savedQ80).sum = (81621574612131188336 : ℤ) ∧
      frozenSavedStrip429.length = 512 - firstU (⟨103, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip429_sum :
    (∑ j : Fin (512 - firstU (⟨103, by decide⟩ : Fin 186)),
      (frozenSavedStrip429.getD j.val default).savedQ80) = (81621574612131188336 : ℤ) := by
  rw [← strip429_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip429_data_checked.1

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip430_data_checked :
    (frozenSavedStrip430.map FrozenSavedRow.savedQ80).sum = (81128592209946224693 : ℤ) ∧
      frozenSavedStrip430.length = 512 - firstU (⟨104, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip430_sum :
    (∑ j : Fin (512 - firstU (⟨104, by decide⟩ : Fin 186)),
      (frozenSavedStrip430.getD j.val default).savedQ80) = (81128592209946224693 : ℤ) := by
  rw [← strip430_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip430_data_checked.1

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip431_data_checked :
    (frozenSavedStrip431.map FrozenSavedRow.savedQ80).sum = (80340164537519463007 : ℤ) ∧
      frozenSavedStrip431.length = 512 - firstU (⟨105, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip431_sum :
    (∑ j : Fin (512 - firstU (⟨105, by decide⟩ : Fin 186)),
      (frozenSavedStrip431.getD j.val default).savedQ80) = (80340164537519463007 : ℤ) := by
  rw [← strip431_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip431_data_checked.1

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip432_data_checked :
    (frozenSavedStrip432.map FrozenSavedRow.savedQ80).sum = (79856498834033134735 : ℤ) ∧
      frozenSavedStrip432.length = 512 - firstU (⟨106, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip432_sum :
    (∑ j : Fin (512 - firstU (⟨106, by decide⟩ : Fin 186)),
      (frozenSavedStrip432.getD j.val default).savedQ80) = (79856498834033134735 : ℤ) := by
  rw [← strip432_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip432_data_checked.1

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip433_data_checked :
    (frozenSavedStrip433.map FrozenSavedRow.savedQ80).sum = (79366390579371522657 : ℤ) ∧
      frozenSavedStrip433.length = 512 - firstU (⟨107, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip433_sum :
    (∑ j : Fin (512 - firstU (⟨107, by decide⟩ : Fin 186)),
      (frozenSavedStrip433.getD j.val default).savedQ80) = (79366390579371522657 : ℤ) := by
  rw [← strip433_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip433_data_checked.1

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip434_data_checked :
    (frozenSavedStrip434.map FrozenSavedRow.savedQ80).sum = (78591326480437679246 : ℤ) ∧
      frozenSavedStrip434.length = 512 - firstU (⟨108, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip434_sum :
    (∑ j : Fin (512 - firstU (⟨108, by decide⟩ : Fin 186)),
      (frozenSavedStrip434.getD j.val default).savedQ80) = (78591326480437679246 : ℤ) := by
  rw [← strip434_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip434_data_checked.1

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip435_data_checked :
    (frozenSavedStrip435.map FrozenSavedRow.savedQ80).sum = (78105230003812111201 : ℤ) ∧
      frozenSavedStrip435.length = 512 - firstU (⟨109, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip435_sum :
    (∑ j : Fin (512 - firstU (⟨109, by decide⟩ : Fin 186)),
      (frozenSavedStrip435.getD j.val default).savedQ80) = (78105230003812111201 : ℤ) := by
  rw [← strip435_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip435_data_checked.1

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip436_data_checked :
    (frozenSavedStrip436.map FrozenSavedRow.savedQ80).sum = (77333126050651047902 : ℤ) ∧
      frozenSavedStrip436.length = 512 - firstU (⟨110, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip436_sum :
    (∑ j : Fin (512 - firstU (⟨110, by decide⟩ : Fin 186)),
      (frozenSavedStrip436.getD j.val default).savedQ80) = (77333126050651047902 : ℤ) := by
  rw [← strip436_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip436_data_checked.1

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip437_data_checked :
    (frozenSavedStrip437.map FrozenSavedRow.savedQ80).sum = (76851069656625674046 : ℤ) ∧
      frozenSavedStrip437.length = 512 - firstU (⟨111, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip437_sum :
    (∑ j : Fin (512 - firstU (⟨111, by decide⟩ : Fin 186)),
      (frozenSavedStrip437.getD j.val default).savedQ80) = (76851069656625674046 : ℤ) := by
  rw [← strip437_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip437_data_checked.1

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip438_data_checked :
    (frozenSavedStrip438.map FrozenSavedRow.savedQ80).sum = (76081948989900395482 : ℤ) ∧
      frozenSavedStrip438.length = 512 - firstU (⟨112, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip438_sum :
    (∑ j : Fin (512 - firstU (⟨112, by decide⟩ : Fin 186)),
      (frozenSavedStrip438.getD j.val default).savedQ80) = (76081948989900395482 : ℤ) := by
  rw [← strip438_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip438_data_checked.1

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip439_data_checked :
    (frozenSavedStrip439.map FrozenSavedRow.savedQ80).sum = (75603961278727556492 : ℤ) ∧
      frozenSavedStrip439.length = 512 - firstU (⟨113, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip439_sum :
    (∑ j : Fin (512 - firstU (⟨113, by decide⟩ : Fin 186)),
      (frozenSavedStrip439.getD j.val default).savedQ80) = (75603961278727556492 : ℤ) := by
  rw [← strip439_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip439_data_checked.1

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip440_data_checked :
    (frozenSavedStrip440.map FrozenSavedRow.savedQ80).sum = (74837847289993523072 : ℤ) ∧
      frozenSavedStrip440.length = 512 - firstU (⟨114, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip440_sum :
    (∑ j : Fin (512 - firstU (⟨114, by decide⟩ : Fin 186)),
      (frozenSavedStrip440.getD j.val default).savedQ80) = (74837847289993523072 : ℤ) := by
  rw [← strip440_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip440_data_checked.1

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip441_data_checked :
    (frozenSavedStrip441.map FrozenSavedRow.savedQ80).sum = (74363957162615728162 : ℤ) ∧
      frozenSavedStrip441.length = 512 - firstU (⟨115, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip441_sum :
    (∑ j : Fin (512 - firstU (⟨115, by decide⟩ : Fin 186)),
      (frozenSavedStrip441.getD j.val default).savedQ80) = (74363957162615728162 : ℤ) := by
  rw [← strip441_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip441_data_checked.1

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip442_data_checked :
    (frozenSavedStrip442.map FrozenSavedRow.savedQ80).sum = (73595972201006097751 : ℤ) ∧
      frozenSavedStrip442.length = 512 - firstU (⟨116, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip442_sum :
    (∑ j : Fin (512 - firstU (⟨116, by decide⟩ : Fin 186)),
      (frozenSavedStrip442.getD j.val default).savedQ80) = (73595972201006097751 : ℤ) := by
  rw [← strip442_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip442_data_checked.1

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip443_data_checked :
    (frozenSavedStrip443.map FrozenSavedRow.savedQ80).sum = (73126203939915137756 : ℤ) ∧
      frozenSavedStrip443.length = 512 - firstU (⟨117, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip443_sum :
    (∑ j : Fin (512 - firstU (⟨117, by decide⟩ : Fin 186)),
      (frozenSavedStrip443.getD j.val default).savedQ80) = (73126203939915137756 : ℤ) := by
  rw [← strip443_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip443_data_checked.1

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip444_data_checked :
    (frozenSavedStrip444.map FrozenSavedRow.savedQ80).sum = (72361257279389387879 : ℤ) ∧
      frozenSavedStrip444.length = 512 - firstU (⟨118, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip444_sum :
    (∑ j : Fin (512 - firstU (⟨118, by decide⟩ : Fin 186)),
      (frozenSavedStrip444.getD j.val default).savedQ80) = (72361257279389387879 : ℤ) := by
  rw [← strip444_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip444_data_checked.1

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip445_data_checked :
    (frozenSavedStrip445.map FrozenSavedRow.savedQ80).sum = (71890649738988413013 : ℤ) ∧
      frozenSavedStrip445.length = 512 - firstU (⟨119, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip445_sum :
    (∑ j : Fin (512 - firstU (⟨119, by decide⟩ : Fin 186)),
      (frozenSavedStrip445.getD j.val default).savedQ80) = (71890649738988413013 : ℤ) := by
  rw [← strip445_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip445_data_checked.1

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip446_data_checked :
    (frozenSavedStrip446.map FrozenSavedRow.savedQ80).sum = (71133756030272390612 : ℤ) ∧
      frozenSavedStrip446.length = 512 - firstU (⟨120, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip446_sum :
    (∑ j : Fin (512 - firstU (⟨120, by decide⟩ : Fin 186)),
      (frozenSavedStrip446.getD j.val default).savedQ80) = (71133756030272390612 : ℤ) := by
  rw [← strip446_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip446_data_checked.1

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip447_data_checked :
    (frozenSavedStrip447.map FrozenSavedRow.savedQ80).sum = (70667318489282676937 : ℤ) ∧
      frozenSavedStrip447.length = 512 - firstU (⟨121, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip447_sum :
    (∑ j : Fin (512 - firstU (⟨121, by decide⟩ : Fin 186)),
      (frozenSavedStrip447.getD j.val default).savedQ80) = (70667318489282676937 : ℤ) := by
  rw [← strip447_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip447_data_checked.1

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip448_data_checked :
    (frozenSavedStrip448.map FrozenSavedRow.savedQ80).sum = (69908438631195592511 : ℤ) ∧
      frozenSavedStrip448.length = 512 - firstU (⟨122, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip448_sum :
    (∑ j : Fin (512 - firstU (⟨122, by decide⟩ : Fin 186)),
      (frozenSavedStrip448.getD j.val default).savedQ80) = (69908438631195592511 : ℤ) := by
  rw [← strip448_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip448_data_checked.1

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip449_data_checked :
    (frozenSavedStrip449.map FrozenSavedRow.savedQ80).sum = (69451284993805651089 : ℤ) ∧
      frozenSavedStrip449.length = 512 - firstU (⟨123, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip449_sum :
    (∑ j : Fin (512 - firstU (⟨123, by decide⟩ : Fin 186)),
      (frozenSavedStrip449.getD j.val default).savedQ80) = (69451284993805651089 : ℤ) := by
  rw [← strip449_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip449_data_checked.1

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip450_data_checked :
    (frozenSavedStrip450.map FrozenSavedRow.savedQ80).sum = (68695516346221929061 : ℤ) ∧
      frozenSavedStrip450.length = 512 - firstU (⟨124, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip450_sum :
    (∑ j : Fin (512 - firstU (⟨124, by decide⟩ : Fin 186)),
      (frozenSavedStrip450.getD j.val default).savedQ80) = (68695516346221929061 : ℤ) := by
  rw [← strip450_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip450_data_checked.1

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip451_data_checked :
    (frozenSavedStrip451.map FrozenSavedRow.savedQ80).sum = (68237422810426890939 : ℤ) ∧
      frozenSavedStrip451.length = 512 - firstU (⟨125, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip451_sum :
    (∑ j : Fin (512 - firstU (⟨125, by decide⟩ : Fin 186)),
      (frozenSavedStrip451.getD j.val default).savedQ80) = (68237422810426890939 : ℤ) := by
  rw [← strip451_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip451_data_checked.1

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip452_data_checked :
    (frozenSavedStrip452.map FrozenSavedRow.savedQ80).sum = (68883469484933383860 : ℤ) ∧
      frozenSavedStrip452.length = 512 - firstU (⟨126, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip452_sum :
    (∑ j : Fin (512 - firstU (⟨126, by decide⟩ : Fin 186)),
      (frozenSavedStrip452.getD j.val default).savedQ80) = (68883469484933383860 : ℤ) := by
  rw [← strip452_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip452_data_checked.1

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip453_data_checked :
    (frozenSavedStrip453.map FrozenSavedRow.savedQ80).sum = (68424663538161026688 : ℤ) ∧
      frozenSavedStrip453.length = 512 - firstU (⟨127, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip453_sum :
    (∑ j : Fin (512 - firstU (⟨127, by decide⟩ : Fin 186)),
      (frozenSavedStrip453.getD j.val default).savedQ80) = (68424663538161026688 : ℤ) := by
  rw [← strip453_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip453_data_checked.1

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip454_data_checked :
    (frozenSavedStrip454.map FrozenSavedRow.savedQ80).sum = (67670113878522421193 : ℤ) ∧
      frozenSavedStrip454.length = 512 - firstU (⟨128, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip454_sum :
    (∑ j : Fin (512 - firstU (⟨128, by decide⟩ : Fin 186)),
      (frozenSavedStrip454.getD j.val default).savedQ80) = (67670113878522421193 : ℤ) := by
  rw [← strip454_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip454_data_checked.1

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip455_data_checked :
    (frozenSavedStrip455.map FrozenSavedRow.savedQ80).sum = (67220854706839842056 : ℤ) ∧
      frozenSavedStrip455.length = 512 - firstU (⟨129, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip455_sum :
    (∑ j : Fin (512 - firstU (⟨129, by decide⟩ : Fin 186)),
      (frozenSavedStrip455.getD j.val default).savedQ80) = (67220854706839842056 : ℤ) := by
  rw [← strip455_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip455_data_checked.1

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip456_data_checked :
    (frozenSavedStrip456.map FrozenSavedRow.savedQ80).sum = (66469462980586265387 : ℤ) ∧
      frozenSavedStrip456.length = 512 - firstU (⟨130, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip456_sum :
    (∑ j : Fin (512 - firstU (⟨130, by decide⟩ : Fin 186)),
      (frozenSavedStrip456.getD j.val default).savedQ80) = (66469462980586265387 : ℤ) := by
  rw [← strip456_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip456_data_checked.1

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip457_data_checked :
    (frozenSavedStrip457.map FrozenSavedRow.savedQ80).sum = (66019119627065224251 : ℤ) ∧
      frozenSavedStrip457.length = 512 - firstU (⟨131, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip457_sum :
    (∑ j : Fin (512 - firstU (⟨131, by decide⟩ : Fin 186)),
      (frozenSavedStrip457.getD j.val default).savedQ80) = (66019119627065224251 : ℤ) := by
  rw [← strip457_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip457_data_checked.1

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip458_data_checked :
    (frozenSavedStrip458.map FrozenSavedRow.savedQ80).sum = (65276301337640967992 : ℤ) ∧
      frozenSavedStrip458.length = 512 - firstU (⟨132, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip458_sum :
    (∑ j : Fin (512 - firstU (⟨132, by decide⟩ : Fin 186)),
      (frozenSavedStrip458.getD j.val default).savedQ80) = (65276301337640967992 : ℤ) := by
  rw [← strip458_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip458_data_checked.1

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip459_data_checked :
    (frozenSavedStrip459.map FrozenSavedRow.savedQ80).sum = (64830283812722531061 : ℤ) ∧
      frozenSavedStrip459.length = 512 - firstU (⟨133, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip459_sum :
    (∑ j : Fin (512 - firstU (⟨133, by decide⟩ : Fin 186)),
      (frozenSavedStrip459.getD j.val default).savedQ80) = (64830283812722531061 : ℤ) := by
  rw [← strip459_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip459_data_checked.1

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip460_data_checked :
    (frozenSavedStrip460.map FrozenSavedRow.savedQ80).sum = (64085184421942373509 : ℤ) ∧
      frozenSavedStrip460.length = 512 - firstU (⟨134, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip460_sum :
    (∑ j : Fin (512 - firstU (⟨134, by decide⟩ : Fin 186)),
      (frozenSavedStrip460.getD j.val default).savedQ80) = (64085184421942373509 : ℤ) := by
  rw [← strip460_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip460_data_checked.1

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip461_data_checked :
    (frozenSavedStrip461.map FrozenSavedRow.savedQ80).sum = (63649026188107698584 : ℤ) ∧
      frozenSavedStrip461.length = 512 - firstU (⟨135, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip461_sum :
    (∑ j : Fin (512 - firstU (⟨135, by decide⟩ : Fin 186)),
      (frozenSavedStrip461.getD j.val default).savedQ80) = (63649026188107698584 : ℤ) := by
  rw [← strip461_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip461_data_checked.1

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip462_data_checked :
    (frozenSavedStrip462.map FrozenSavedRow.savedQ80).sum = (63211374834864996327 : ℤ) ∧
      frozenSavedStrip462.length = 512 - firstU (⟨136, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip462_sum :
    (∑ j : Fin (512 - firstU (⟨136, by decide⟩ : Fin 186)),
      (frozenSavedStrip462.getD j.val default).savedQ80) = (63211374834864996327 : ℤ) := by
  rw [← strip462_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip462_data_checked.1

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip463_data_checked :
    (frozenSavedStrip463.map FrozenSavedRow.savedQ80).sum = (62475404898209301638 : ℤ) ∧
      frozenSavedStrip463.length = 512 - firstU (⟨137, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip463_sum :
    (∑ j : Fin (512 - firstU (⟨137, by decide⟩ : Fin 186)),
      (frozenSavedStrip463.getD j.val default).savedQ80) = (62475404898209301638 : ℤ) := by
  rw [← strip463_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip463_data_checked.1

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip464_data_checked :
    (frozenSavedStrip464.map FrozenSavedRow.savedQ80).sum = (62042164686385365196 : ℤ) ∧
      frozenSavedStrip464.length = 512 - firstU (⟨138, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip464_sum :
    (∑ j : Fin (512 - firstU (⟨138, by decide⟩ : Fin 186)),
      (frozenSavedStrip464.getD j.val default).savedQ80) = (62042164686385365196 : ℤ) := by
  rw [← strip464_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip464_data_checked.1

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip465_data_checked :
    (frozenSavedStrip465.map FrozenSavedRow.savedQ80).sum = (61309478719747058462 : ℤ) ∧
      frozenSavedStrip465.length = 512 - firstU (⟨139, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip465_sum :
    (∑ j : Fin (512 - firstU (⟨139, by decide⟩ : Fin 186)),
      (frozenSavedStrip465.getD j.val default).savedQ80) = (61309478719747058462 : ℤ) := by
  rw [← strip465_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip465_data_checked.1

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip466_data_checked :
    (frozenSavedStrip466.map FrozenSavedRow.savedQ80).sum = (60880682256022128268 : ℤ) ∧
      frozenSavedStrip466.length = 512 - firstU (⟨140, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip466_sum :
    (∑ j : Fin (512 - firstU (⟨140, by decide⟩ : Fin 186)),
      (frozenSavedStrip466.getD j.val default).savedQ80) = (60880682256022128268 : ℤ) := by
  rw [← strip466_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip466_data_checked.1

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip467_data_checked :
    (frozenSavedStrip467.map FrozenSavedRow.savedQ80).sum = (60151307059771961839 : ℤ) ∧
      frozenSavedStrip467.length = 512 - firstU (⟨141, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip467_sum :
    (∑ j : Fin (512 - firstU (⟨141, by decide⟩ : Fin 186)),
      (frozenSavedStrip467.getD j.val default).savedQ80) = (60151307059771961839 : ℤ) := by
  rw [← strip467_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip467_data_checked.1

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip468_data_checked :
    (frozenSavedStrip468.map FrozenSavedRow.savedQ80).sum = (59726987303109246651 : ℤ) ∧
      frozenSavedStrip468.length = 512 - firstU (⟨142, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip468_sum :
    (∑ j : Fin (512 - firstU (⟨142, by decide⟩ : Fin 186)),
      (frozenSavedStrip468.getD j.val default).savedQ80) = (59726987303109246651 : ℤ) := by
  rw [← strip468_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip468_data_checked.1

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip469_data_checked :
    (frozenSavedStrip469.map FrozenSavedRow.savedQ80).sum = (60321861211913925951 : ℤ) ∧
      frozenSavedStrip469.length = 512 - firstU (⟨143, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip469_sum :
    (∑ j : Fin (512 - firstU (⟨143, by decide⟩ : Fin 186)),
      (frozenSavedStrip469.getD j.val default).savedQ80) = (60321861211913925951 : ℤ) := by
  rw [← strip469_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip469_data_checked.1

end ImbalancedChen.P2HistoricalSavedFloorStoredTotal
