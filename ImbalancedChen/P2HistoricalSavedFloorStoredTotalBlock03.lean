import ImbalancedChen.P2HistoricalSavedFloorStoredTotalCore
import ImbalancedChen.P2HistoricalSavedFloorStripData470
import ImbalancedChen.P2HistoricalSavedFloorStripData471
import ImbalancedChen.P2HistoricalSavedFloorStripData472
import ImbalancedChen.P2HistoricalSavedFloorStripData473
import ImbalancedChen.P2HistoricalSavedFloorStripData474
import ImbalancedChen.P2HistoricalSavedFloorStripData475
import ImbalancedChen.P2HistoricalSavedFloorStripData476
import ImbalancedChen.P2HistoricalSavedFloorStripData477
import ImbalancedChen.P2HistoricalSavedFloorStripData478
import ImbalancedChen.P2HistoricalSavedFloorStripData479
import ImbalancedChen.P2HistoricalSavedFloorStripData480
import ImbalancedChen.P2HistoricalSavedFloorStripData481
import ImbalancedChen.P2HistoricalSavedFloorStripData482
import ImbalancedChen.P2HistoricalSavedFloorStripData483
import ImbalancedChen.P2HistoricalSavedFloorStripData484
import ImbalancedChen.P2HistoricalSavedFloorStripData485
import ImbalancedChen.P2HistoricalSavedFloorStripData486
import ImbalancedChen.P2HistoricalSavedFloorStripData487
import ImbalancedChen.P2HistoricalSavedFloorStripData488
import ImbalancedChen.P2HistoricalSavedFloorStripData489
import ImbalancedChen.P2HistoricalSavedFloorStripData490
import ImbalancedChen.P2HistoricalSavedFloorStripData491
import ImbalancedChen.P2HistoricalSavedFloorStripData492
import ImbalancedChen.P2HistoricalSavedFloorStripData493
import ImbalancedChen.P2HistoricalSavedFloorStripData494
import ImbalancedChen.P2HistoricalSavedFloorStripData495
import ImbalancedChen.P2HistoricalSavedFloorStripData496
import ImbalancedChen.P2HistoricalSavedFloorStripData497
import ImbalancedChen.P2HistoricalSavedFloorStripData498
import ImbalancedChen.P2HistoricalSavedFloorStripData499
import ImbalancedChen.P2HistoricalSavedFloorStripData500
import ImbalancedChen.P2HistoricalSavedFloorStripData501
import ImbalancedChen.P2HistoricalSavedFloorStripData502
import ImbalancedChen.P2HistoricalSavedFloorStripData503
import ImbalancedChen.P2HistoricalSavedFloorStripData504
import ImbalancedChen.P2HistoricalSavedFloorStripData505
import ImbalancedChen.P2HistoricalSavedFloorStripData506
import ImbalancedChen.P2HistoricalSavedFloorStripData507
import ImbalancedChen.P2HistoricalSavedFloorStripData508
import ImbalancedChen.P2HistoricalSavedFloorStripData509
import ImbalancedChen.P2HistoricalSavedFloorStripData510
import ImbalancedChen.P2HistoricalSavedFloorStripData511

namespace ImbalancedChen.P2HistoricalSavedFloorStoredTotal
open P2HistoricalSavedFloorRowsBinder
open Certificates.PairedV2 Certificates.PairedV2.FullMask
open scoped BigOperators
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip470_data_checked :
    (frozenSavedStrip470.map FrozenSavedRow.savedQ80).sum = (58576006461426349305 : ℤ) ∧
      frozenSavedStrip470.length = 512 - firstU (⟨144, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip470_sum :
    (∑ j : Fin (512 - firstU (⟨144, by decide⟩ : Fin 186)),
      (frozenSavedStrip470.getD j.val default).savedQ80) = (58576006461426349305 : ℤ) := by
  rw [← strip470_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip470_data_checked.1

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip471_data_checked :
    (frozenSavedStrip471.map FrozenSavedRow.savedQ80).sum = (57853329054051698032 : ℤ) ∧
      frozenSavedStrip471.length = 512 - firstU (⟨145, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip471_sum :
    (∑ j : Fin (512 - firstU (⟨145, by decide⟩ : Fin 186)),
      (frozenSavedStrip471.getD j.val default).savedQ80) = (57853329054051698032 : ℤ) := by
  rw [← strip471_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip471_data_checked.1

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip472_data_checked :
    (frozenSavedStrip472.map FrozenSavedRow.savedQ80).sum = (57432911856859734391 : ℤ) ∧
      frozenSavedStrip472.length = 512 - firstU (⟨146, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip472_sum :
    (∑ j : Fin (512 - firstU (⟨146, by decide⟩ : Fin 186)),
      (frozenSavedStrip472.getD j.val default).savedQ80) = (57432911856859734391 : ℤ) := by
  rw [← strip472_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip472_data_checked.1

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip473_data_checked :
    (frozenSavedStrip473.map FrozenSavedRow.savedQ80).sum = (56713622011690814446 : ℤ) ∧
      frozenSavedStrip473.length = 512 - firstU (⟨147, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip473_sum :
    (∑ j : Fin (512 - firstU (⟨147, by decide⟩ : Fin 186)),
      (frozenSavedStrip473.getD j.val default).savedQ80) = (56713622011690814446 : ℤ) := by
  rw [← strip473_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip473_data_checked.1

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip474_data_checked :
    (frozenSavedStrip474.map FrozenSavedRow.savedQ80).sum = (57597683441832855952 : ℤ) ∧
      frozenSavedStrip474.length = 512 - firstU (⟨148, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip474_sum :
    (∑ j : Fin (512 - firstU (⟨148, by decide⟩ : Fin 186)),
      (frozenSavedStrip474.getD j.val default).savedQ80) = (57597683441832855952 : ℤ) := by
  rw [← strip474_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip474_data_checked.1

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip475_data_checked :
    (frozenSavedStrip475.map FrozenSavedRow.savedQ80).sum = (56876539116289621026 : ℤ) ∧
      frozenSavedStrip475.length = 512 - firstU (⟨149, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip475_sum :
    (∑ j : Fin (512 - firstU (⟨149, by decide⟩ : Fin 186)),
      (frozenSavedStrip475.getD j.val default).savedQ80) = (56876539116289621026 : ℤ) := by
  rw [← strip475_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip475_data_checked.1

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip476_data_checked :
    (frozenSavedStrip476.map FrozenSavedRow.savedQ80).sum = (56459991174818519650 : ℤ) ∧
      frozenSavedStrip476.length = 512 - firstU (⟨150, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip476_sum :
    (∑ j : Fin (512 - firstU (⟨150, by decide⟩ : Fin 186)),
      (frozenSavedStrip476.getD j.val default).savedQ80) = (56459991174818519650 : ℤ) := by
  rw [← strip476_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip476_data_checked.1

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip477_data_checked :
    (frozenSavedStrip477.map FrozenSavedRow.savedQ80).sum = (55737007254502716862 : ℤ) ∧
      frozenSavedStrip477.length = 512 - firstU (⟨151, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip477_sum :
    (∑ j : Fin (512 - firstU (⟨151, by decide⟩ : Fin 186)),
      (frozenSavedStrip477.getD j.val default).savedQ80) = (55737007254502716862 : ℤ) := by
  rw [← strip477_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip477_data_checked.1

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip478_data_checked :
    (frozenSavedStrip478.map FrozenSavedRow.savedQ80).sum = (55330309942475647433 : ℤ) ∧
      frozenSavedStrip478.length = 512 - firstU (⟨152, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip478_sum :
    (∑ j : Fin (512 - firstU (⟨152, by decide⟩ : Fin 186)),
      (frozenSavedStrip478.getD j.val default).savedQ80) = (55330309942475647433 : ℤ) := by
  rw [← strip478_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip478_data_checked.1

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip479_data_checked :
    (frozenSavedStrip479.map FrozenSavedRow.savedQ80).sum = (54610755033766650292 : ℤ) ∧
      frozenSavedStrip479.length = 512 - firstU (⟨153, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip479_sum :
    (∑ j : Fin (512 - firstU (⟨153, by decide⟩ : Fin 186)),
      (frozenSavedStrip479.getD j.val default).savedQ80) = (54610755033766650292 : ℤ) := by
  rw [← strip479_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip479_data_checked.1

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip480_data_checked :
    (frozenSavedStrip480.map FrozenSavedRow.savedQ80).sum = (54203351264098340894 : ℤ) ∧
      frozenSavedStrip480.length = 512 - firstU (⟨154, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip480_sum :
    (∑ j : Fin (512 - firstU (⟨154, by decide⟩ : Fin 186)),
      (frozenSavedStrip480.getD j.val default).savedQ80) = (54203351264098340894 : ℤ) := by
  rw [← strip480_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip480_data_checked.1

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip481_data_checked :
    (frozenSavedStrip481.map FrozenSavedRow.savedQ80).sum = (53492605474195764124 : ℤ) ∧
      frozenSavedStrip481.length = 512 - firstU (⟨155, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip481_sum :
    (∑ j : Fin (512 - firstU (⟨155, by decide⟩ : Fin 186)),
      (frozenSavedStrip481.getD j.val default).savedQ80) = (53492605474195764124 : ℤ) := by
  rw [← strip481_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip481_data_checked.1

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip482_data_checked :
    (frozenSavedStrip482.map FrozenSavedRow.savedQ80).sum = (53089869617503987213 : ℤ) ∧
      frozenSavedStrip482.length = 512 - firstU (⟨156, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip482_sum :
    (∑ j : Fin (512 - firstU (⟨156, by decide⟩ : Fin 186)),
      (frozenSavedStrip482.getD j.val default).savedQ80) = (53089869617503987213 : ℤ) := by
  rw [← strip482_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip482_data_checked.1

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip483_data_checked :
    (frozenSavedStrip483.map FrozenSavedRow.savedQ80).sum = (52377167532333803412 : ℤ) ∧
      frozenSavedStrip483.length = 512 - firstU (⟨157, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip483_sum :
    (∑ j : Fin (512 - firstU (⟨157, by decide⟩ : Fin 186)),
      (frozenSavedStrip483.getD j.val default).savedQ80) = (52377167532333803412 : ℤ) := by
  rw [← strip483_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip483_data_checked.1

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip484_data_checked :
    (frozenSavedStrip484.map FrozenSavedRow.savedQ80).sum = (51984590185087987492 : ℤ) ∧
      frozenSavedStrip484.length = 512 - firstU (⟨158, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip484_sum :
    (∑ j : Fin (512 - firstU (⟨158, by decide⟩ : Fin 186)),
      (frozenSavedStrip484.getD j.val default).savedQ80) = (51984590185087987492 : ℤ) := by
  rw [← strip484_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip484_data_checked.1

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip485_data_checked :
    (frozenSavedStrip485.map FrozenSavedRow.savedQ80).sum = (51275403728146498594 : ℤ) ∧
      frozenSavedStrip485.length = 512 - firstU (⟨159, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip485_sum :
    (∑ j : Fin (512 - firstU (⟨159, by decide⟩ : Fin 186)),
      (frozenSavedStrip485.getD j.val default).savedQ80) = (51275403728146498594 : ℤ) := by
  rw [← strip485_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip485_data_checked.1

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip486_data_checked :
    (frozenSavedStrip486.map FrozenSavedRow.savedQ80).sum = (50882014589560360901 : ℤ) ∧
      frozenSavedStrip486.length = 512 - firstU (⟨160, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip486_sum :
    (∑ j : Fin (512 - firstU (⟨160, by decide⟩ : Fin 186)),
      (frozenSavedStrip486.getD j.val default).savedQ80) = (50882014589560360901 : ℤ) := by
  rw [← strip486_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip486_data_checked.1

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip487_data_checked :
    (frozenSavedStrip487.map FrozenSavedRow.savedQ80).sum = (50181936800883388301 : ℤ) ∧
      frozenSavedStrip487.length = 512 - firstU (⟨161, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip487_sum :
    (∑ j : Fin (512 - firstU (⟨161, by decide⟩ : Fin 186)),
      (frozenSavedStrip487.getD j.val default).savedQ80) = (50181936800883388301 : ℤ) := by
  rw [← strip487_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip487_data_checked.1

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip488_data_checked :
    (frozenSavedStrip488.map FrozenSavedRow.savedQ80).sum = (49793323120696811151 : ℤ) ∧
      frozenSavedStrip488.length = 512 - firstU (⟨162, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip488_sum :
    (∑ j : Fin (512 - firstU (⟨162, by decide⟩ : Fin 186)),
      (frozenSavedStrip488.getD j.val default).savedQ80) = (49793323120696811151 : ℤ) := by
  rw [← strip488_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip488_data_checked.1

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip489_data_checked :
    (frozenSavedStrip489.map FrozenSavedRow.savedQ80).sum = (50324778442836129942 : ℤ) ∧
      frozenSavedStrip489.length = 512 - firstU (⟨163, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip489_sum :
    (∑ j : Fin (512 - firstU (⟨163, by decide⟩ : Fin 186)),
      (frozenSavedStrip489.getD j.val default).savedQ80) = (50324778442836129942 : ℤ) := by
  rw [← strip489_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip489_data_checked.1

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip490_data_checked :
    (frozenSavedStrip490.map FrozenSavedRow.savedQ80).sum = (49941171188073857715 : ℤ) ∧
      frozenSavedStrip490.length = 512 - firstU (⟨164, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip490_sum :
    (∑ j : Fin (512 - firstU (⟨164, by decide⟩ : Fin 186)),
      (frozenSavedStrip490.getD j.val default).savedQ80) = (49941171188073857715 : ℤ) := by
  rw [← strip490_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip490_data_checked.1

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip491_data_checked :
    (frozenSavedStrip491.map FrozenSavedRow.savedQ80).sum = (49550922453986107242 : ℤ) ∧
      frozenSavedStrip491.length = 512 - firstU (⟨165, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip491_sum :
    (∑ j : Fin (512 - firstU (⟨165, by decide⟩ : Fin 186)),
      (frozenSavedStrip491.getD j.val default).savedQ80) = (49550922453986107242 : ℤ) := by
  rw [← strip491_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip491_data_checked.1

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip492_data_checked :
    (frozenSavedStrip492.map FrozenSavedRow.savedQ80).sum = (48858332213896737686 : ℤ) ∧
      frozenSavedStrip492.length = 512 - firstU (⟨166, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip492_sum :
    (∑ j : Fin (512 - firstU (⟨166, by decide⟩ : Fin 186)),
      (frozenSavedStrip492.getD j.val default).savedQ80) = (48858332213896737686 : ℤ) := by
  rw [← strip492_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip492_data_checked.1

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip493_data_checked :
    (frozenSavedStrip493.map FrozenSavedRow.savedQ80).sum = (48472911677967673485 : ℤ) ∧
      frozenSavedStrip493.length = 512 - firstU (⟨167, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip493_sum :
    (∑ j : Fin (512 - firstU (⟨167, by decide⟩ : Fin 186)),
      (frozenSavedStrip493.getD j.val default).savedQ80) = (48472911677967673485 : ℤ) := by
  rw [← strip493_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip493_data_checked.1

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip494_data_checked :
    (frozenSavedStrip494.map FrozenSavedRow.savedQ80).sum = (47783962802832455194 : ℤ) ∧
      frozenSavedStrip494.length = 512 - firstU (⟨168, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip494_sum :
    (∑ j : Fin (512 - firstU (⟨168, by decide⟩ : Fin 186)),
      (frozenSavedStrip494.getD j.val default).savedQ80) = (47783962802832455194 : ℤ) := by
  rw [← strip494_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip494_data_checked.1

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip495_data_checked :
    (frozenSavedStrip495.map FrozenSavedRow.savedQ80).sum = (47403407790173486680 : ℤ) ∧
      frozenSavedStrip495.length = 512 - firstU (⟨169, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip495_sum :
    (∑ j : Fin (512 - firstU (⟨169, by decide⟩ : Fin 186)),
      (frozenSavedStrip495.getD j.val default).savedQ80) = (47403407790173486680 : ℤ) := by
  rw [← strip495_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip495_data_checked.1

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip496_data_checked :
    (frozenSavedStrip496.map FrozenSavedRow.savedQ80).sum = (46718131218554596898 : ℤ) ∧
      frozenSavedStrip496.length = 512 - firstU (⟨170, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip496_sum :
    (∑ j : Fin (512 - firstU (⟨170, by decide⟩ : Fin 186)),
      (frozenSavedStrip496.getD j.val default).savedQ80) = (46718131218554596898 : ℤ) := by
  rw [← strip496_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip496_data_checked.1

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip497_data_checked :
    (frozenSavedStrip497.map FrozenSavedRow.savedQ80).sum = (46342479463071697558 : ℤ) ∧
      frozenSavedStrip497.length = 512 - firstU (⟨171, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip497_sum :
    (∑ j : Fin (512 - firstU (⟨171, by decide⟩ : Fin 186)),
      (frozenSavedStrip497.getD j.val default).savedQ80) = (46342479463071697558 : ℤ) := by
  rw [← strip497_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip497_data_checked.1

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip498_data_checked :
    (frozenSavedStrip498.map FrozenSavedRow.savedQ80).sum = (45660906474400475204 : ℤ) ∧
      frozenSavedStrip498.length = 512 - firstU (⟨172, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip498_sum :
    (∑ j : Fin (512 - firstU (⟨172, by decide⟩ : Fin 186)),
      (frozenSavedStrip498.getD j.val default).savedQ80) = (45660906474400475204 : ℤ) := by
  rw [← strip498_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip498_data_checked.1

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip499_data_checked :
    (frozenSavedStrip499.map FrozenSavedRow.savedQ80).sum = (45290196114887701249 : ℤ) ∧
      frozenSavedStrip499.length = 512 - firstU (⟨173, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip499_sum :
    (∑ j : Fin (512 - firstU (⟨173, by decide⟩ : Fin 186)),
      (frozenSavedStrip499.getD j.val default).savedQ80) = (45290196114887701249 : ℤ) := by
  rw [← strip499_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip499_data_checked.1

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip500_data_checked :
    (frozenSavedStrip500.map FrozenSavedRow.savedQ80).sum = (44606960657686448424 : ℤ) ∧
      frozenSavedStrip500.length = 512 - firstU (⟨174, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip500_sum :
    (∑ j : Fin (512 - firstU (⟨174, by decide⟩ : Fin 186)),
      (frozenSavedStrip500.getD j.val default).savedQ80) = (44606960657686448424 : ℤ) := by
  rw [← strip500_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip500_data_checked.1

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip501_data_checked :
    (frozenSavedStrip501.map FrozenSavedRow.savedQ80).sum = (44241224414016342930 : ℤ) ∧
      frozenSavedStrip501.length = 512 - firstU (⟨175, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip501_sum :
    (∑ j : Fin (512 - firstU (⟨175, by decide⟩ : Fin 186)),
      (frozenSavedStrip501.getD j.val default).savedQ80) = (44241224414016342930 : ℤ) := by
  rw [← strip501_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip501_data_checked.1

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip502_data_checked :
    (frozenSavedStrip502.map FrozenSavedRow.savedQ80).sum = (43561737102615638743 : ℤ) ∧
      frozenSavedStrip502.length = 512 - firstU (⟨176, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip502_sum :
    (∑ j : Fin (512 - firstU (⟨176, by decide⟩ : Fin 186)),
      (frozenSavedStrip502.getD j.val default).savedQ80) = (43561737102615638743 : ℤ) := by
  rw [← strip502_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip502_data_checked.1

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip503_data_checked :
    (frozenSavedStrip503.map FrozenSavedRow.savedQ80).sum = (43201013882675728606 : ℤ) ∧
      frozenSavedStrip503.length = 512 - firstU (⟨177, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip503_sum :
    (∑ j : Fin (512 - firstU (⟨177, by decide⟩ : Fin 186)),
      (frozenSavedStrip503.getD j.val default).savedQ80) = (43201013882675728606 : ℤ) := by
  rw [← strip503_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip503_data_checked.1

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip504_data_checked :
    (frozenSavedStrip504.map FrozenSavedRow.savedQ80).sum = (42525306911711509668 : ℤ) ∧
      frozenSavedStrip504.length = 512 - firstU (⟨178, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip504_sum :
    (∑ j : Fin (512 - firstU (⟨178, by decide⟩ : Fin 186)),
      (frozenSavedStrip504.getD j.val default).savedQ80) = (42525306911711509668 : ℤ) := by
  rw [← strip504_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip504_data_checked.1

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip505_data_checked :
    (frozenSavedStrip505.map FrozenSavedRow.savedQ80).sum = (42169636042355854200 : ℤ) ∧
      frozenSavedStrip505.length = 512 - firstU (⟨179, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip505_sum :
    (∑ j : Fin (512 - firstU (⟨179, by decide⟩ : Fin 186)),
      (frozenSavedStrip505.getD j.val default).savedQ80) = (42169636042355854200 : ℤ) := by
  rw [← strip505_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip505_data_checked.1

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip506_data_checked :
    (frozenSavedStrip506.map FrozenSavedRow.savedQ80).sum = (41497741968113308085 : ℤ) ∧
      frozenSavedStrip506.length = 512 - firstU (⟨180, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip506_sum :
    (∑ j : Fin (512 - firstU (⟨180, by decide⟩ : Fin 186)),
      (frozenSavedStrip506.getD j.val default).savedQ80) = (41497741968113308085 : ℤ) := by
  rw [← strip506_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip506_data_checked.1

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip507_data_checked :
    (frozenSavedStrip507.map FrozenSavedRow.savedQ80).sum = (42299832350738889492 : ℤ) ∧
      frozenSavedStrip507.length = 512 - firstU (⟨181, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip507_sum :
    (∑ j : Fin (512 - firstU (⟨181, by decide⟩ : Fin 186)),
      (frozenSavedStrip507.getD j.val default).savedQ80) = (42299832350738889492 : ℤ) := by
  rw [← strip507_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip507_data_checked.1

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip508_data_checked :
    (frozenSavedStrip508.map FrozenSavedRow.savedQ80).sum = (41626030631623545566 : ℤ) ∧
      frozenSavedStrip508.length = 512 - firstU (⟨182, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip508_sum :
    (∑ j : Fin (512 - firstU (⟨182, by decide⟩ : Fin 186)),
      (frozenSavedStrip508.getD j.val default).savedQ80) = (41626030631623545566 : ℤ) := by
  rw [← strip508_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip508_data_checked.1

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip509_data_checked :
    (frozenSavedStrip509.map FrozenSavedRow.savedQ80).sum = (41269275258383203157 : ℤ) ∧
      frozenSavedStrip509.length = 512 - firstU (⟨183, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip509_sum :
    (∑ j : Fin (512 - firstU (⟨183, by decide⟩ : Fin 186)),
      (frozenSavedStrip509.getD j.val default).savedQ80) = (41269275258383203157 : ℤ) := by
  rw [← strip509_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip509_data_checked.1

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip510_data_checked :
    (frozenSavedStrip510.map FrozenSavedRow.savedQ80).sum = (40604856012710529037 : ℤ) ∧
      frozenSavedStrip510.length = 512 - firstU (⟨184, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip510_sum :
    (∑ j : Fin (512 - firstU (⟨184, by decide⟩ : Fin 186)),
      (frozenSavedStrip510.getD j.val default).savedQ80) = (40604856012710529037 : ℤ) := by
  rw [← strip510_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip510_data_checked.1

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip511_data_checked :
    (frozenSavedStrip511.map FrozenSavedRow.savedQ80).sum = (40253225100893230709 : ℤ) ∧
      frozenSavedStrip511.length = 512 - firstU (⟨185, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip511_sum :
    (∑ j : Fin (512 - firstU (⟨185, by decide⟩ : Fin 186)),
      (frozenSavedStrip511.getD j.val default).savedQ80) = (40253225100893230709 : ℤ) := by
  rw [← strip511_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip511_data_checked.1

end ImbalancedChen.P2HistoricalSavedFloorStoredTotal
