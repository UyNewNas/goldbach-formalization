import ImbalancedChen.P2HistoricalSavedFloorStoredTotalCore
import ImbalancedChen.P2HistoricalSavedFloorStripData326
import ImbalancedChen.P2HistoricalSavedFloorStripData327
import ImbalancedChen.P2HistoricalSavedFloorStripData328
import ImbalancedChen.P2HistoricalSavedFloorStripData329
import ImbalancedChen.P2HistoricalSavedFloorStripData330
import ImbalancedChen.P2HistoricalSavedFloorStripData331
import ImbalancedChen.P2HistoricalSavedFloorStripData332
import ImbalancedChen.P2HistoricalSavedFloorStripData333
import ImbalancedChen.P2HistoricalSavedFloorStripData334
import ImbalancedChen.P2HistoricalSavedFloorStripData335
import ImbalancedChen.P2HistoricalSavedFloorStripData336
import ImbalancedChen.P2HistoricalSavedFloorStripData337
import ImbalancedChen.P2HistoricalSavedFloorStripData338
import ImbalancedChen.P2HistoricalSavedFloorStripData339
import ImbalancedChen.P2HistoricalSavedFloorStripData340
import ImbalancedChen.P2HistoricalSavedFloorStripData341
import ImbalancedChen.P2HistoricalSavedFloorStripData342
import ImbalancedChen.P2HistoricalSavedFloorStripData343
import ImbalancedChen.P2HistoricalSavedFloorStripData344
import ImbalancedChen.P2HistoricalSavedFloorStripData345
import ImbalancedChen.P2HistoricalSavedFloorStripData346
import ImbalancedChen.P2HistoricalSavedFloorStripData347
import ImbalancedChen.P2HistoricalSavedFloorStripData348
import ImbalancedChen.P2HistoricalSavedFloorStripData349
import ImbalancedChen.P2HistoricalSavedFloorStripData350
import ImbalancedChen.P2HistoricalSavedFloorStripData351
import ImbalancedChen.P2HistoricalSavedFloorStripData352
import ImbalancedChen.P2HistoricalSavedFloorStripData353
import ImbalancedChen.P2HistoricalSavedFloorStripData354
import ImbalancedChen.P2HistoricalSavedFloorStripData355
import ImbalancedChen.P2HistoricalSavedFloorStripData356
import ImbalancedChen.P2HistoricalSavedFloorStripData357
import ImbalancedChen.P2HistoricalSavedFloorStripData358
import ImbalancedChen.P2HistoricalSavedFloorStripData359
import ImbalancedChen.P2HistoricalSavedFloorStripData360
import ImbalancedChen.P2HistoricalSavedFloorStripData361
import ImbalancedChen.P2HistoricalSavedFloorStripData362
import ImbalancedChen.P2HistoricalSavedFloorStripData363
import ImbalancedChen.P2HistoricalSavedFloorStripData364
import ImbalancedChen.P2HistoricalSavedFloorStripData365
import ImbalancedChen.P2HistoricalSavedFloorStripData366
import ImbalancedChen.P2HistoricalSavedFloorStripData367
import ImbalancedChen.P2HistoricalSavedFloorStripData368
import ImbalancedChen.P2HistoricalSavedFloorStripData369
import ImbalancedChen.P2HistoricalSavedFloorStripData370
import ImbalancedChen.P2HistoricalSavedFloorStripData371
import ImbalancedChen.P2HistoricalSavedFloorStripData372
import ImbalancedChen.P2HistoricalSavedFloorStripData373

namespace ImbalancedChen.P2HistoricalSavedFloorStoredTotal
open P2HistoricalSavedFloorRowsBinder
open Certificates.PairedV2 Certificates.PairedV2.FullMask
open scoped BigOperators
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip326_data_checked :
    (frozenSavedStrip326.map FrozenSavedRow.savedQ80).sum = (1878933774938557092 : ℤ) ∧
      frozenSavedStrip326.length = 512 - firstU (⟨0, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip326_sum :
    (∑ j : Fin (512 - firstU (⟨0, by decide⟩ : Fin 186)),
      (frozenSavedStrip326.getD j.val default).savedQ80) = (1878933774938557092 : ℤ) := by
  rw [← strip326_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip326_data_checked.1

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip327_data_checked :
    (frozenSavedStrip327.map FrozenSavedRow.savedQ80).sum = (3739528744218871846 : ℤ) ∧
      frozenSavedStrip327.length = 512 - firstU (⟨1, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip327_sum :
    (∑ j : Fin (512 - firstU (⟨1, by decide⟩ : Fin 186)),
      (frozenSavedStrip327.getD j.val default).savedQ80) = (3739528744218871846 : ℤ) := by
  rw [← strip327_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip327_data_checked.1

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip328_data_checked :
    (frozenSavedStrip328.map FrozenSavedRow.savedQ80).sum = (5581698956890702623 : ℤ) ∧
      frozenSavedStrip328.length = 512 - firstU (⟨2, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip328_sum :
    (∑ j : Fin (512 - firstU (⟨2, by decide⟩ : Fin 186)),
      (frozenSavedStrip328.getD j.val default).savedQ80) = (5581698956890702623 : ℤ) := by
  rw [← strip328_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip328_data_checked.1

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip329_data_checked :
    (frozenSavedStrip329.map FrozenSavedRow.savedQ80).sum = (7409476840812841656 : ℤ) ∧
      frozenSavedStrip329.length = 512 - firstU (⟨3, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip329_sum :
    (∑ j : Fin (512 - firstU (⟨3, by decide⟩ : Fin 186)),
      (frozenSavedStrip329.getD j.val default).savedQ80) = (7409476840812841656 : ℤ) := by
  rw [← strip329_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip329_data_checked.1

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip330_data_checked :
    (frozenSavedStrip330.map FrozenSavedRow.savedQ80).sum = (9218663137600588279 : ℤ) ∧
      frozenSavedStrip330.length = 512 - firstU (⟨4, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip330_sum :
    (∑ j : Fin (512 - firstU (⟨4, by decide⟩ : Fin 186)),
      (frozenSavedStrip330.getD j.val default).savedQ80) = (9218663137600588279 : ℤ) := by
  rw [← strip330_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip330_data_checked.1

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip331_data_checked :
    (frozenSavedStrip331.map FrozenSavedRow.savedQ80).sum = (11013297164532975245 : ℤ) ∧
      frozenSavedStrip331.length = 512 - firstU (⟨5, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip331_sum :
    (∑ j : Fin (512 - firstU (⟨5, by decide⟩ : Fin 186)),
      (frozenSavedStrip331.getD j.val default).savedQ80) = (11013297164532975245 : ℤ) := by
  rw [← strip331_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip331_data_checked.1

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip332_data_checked :
    (frozenSavedStrip332.map FrozenSavedRow.savedQ80).sum = (12785041168942599196 : ℤ) ∧
      frozenSavedStrip332.length = 512 - firstU (⟨6, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip332_sum :
    (∑ j : Fin (512 - firstU (⟨6, by decide⟩ : Fin 186)),
      (frozenSavedStrip332.getD j.val default).savedQ80) = (12785041168942599196 : ℤ) := by
  rw [← strip332_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip332_data_checked.1

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip333_data_checked :
    (frozenSavedStrip333.map FrozenSavedRow.savedQ80).sum = (14542064496731843928 : ℤ) ∧
      frozenSavedStrip333.length = 512 - firstU (⟨7, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip333_sum :
    (∑ j : Fin (512 - firstU (⟨7, by decide⟩ : Fin 186)),
      (frozenSavedStrip333.getD j.val default).savedQ80) = (14542064496731843928 : ℤ) := by
  rw [← strip333_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip333_data_checked.1

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip334_data_checked :
    (frozenSavedStrip334.map FrozenSavedRow.savedQ80).sum = (16276012586846795368 : ℤ) ∧
      frozenSavedStrip334.length = 512 - firstU (⟨8, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip334_sum :
    (∑ j : Fin (512 - firstU (⟨8, by decide⟩ : Fin 186)),
      (frozenSavedStrip334.getD j.val default).savedQ80) = (16276012586846795368 : ℤ) := by
  rw [← strip334_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip334_data_checked.1

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip335_data_checked :
    (frozenSavedStrip335.map FrozenSavedRow.savedQ80).sum = (16144677483770159531 : ℤ) ∧
      frozenSavedStrip335.length = 512 - firstU (⟨9, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip335_sum :
    (∑ j : Fin (512 - firstU (⟨9, by decide⟩ : Fin 186)),
      (frozenSavedStrip335.getD j.val default).savedQ80) = (16144677483770159531 : ℤ) := by
  rw [← strip335_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip335_data_checked.1

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip336_data_checked :
    (frozenSavedStrip336.map FrozenSavedRow.savedQ80).sum = (17844146246146058095 : ℤ) ∧
      frozenSavedStrip336.length = 512 - firstU (⟨10, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip336_sum :
    (∑ j : Fin (512 - firstU (⟨10, by decide⟩ : Fin 186)),
      (frozenSavedStrip336.getD j.val default).savedQ80) = (17844146246146058095 : ℤ) := by
  rw [← strip336_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip336_data_checked.1

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip337_data_checked :
    (frozenSavedStrip337.map FrozenSavedRow.savedQ80).sum = (19524410347656738443 : ℤ) ∧
      frozenSavedStrip337.length = 512 - firstU (⟨11, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip337_sum :
    (∑ j : Fin (512 - firstU (⟨11, by decide⟩ : Fin 186)),
      (frozenSavedStrip337.getD j.val default).savedQ80) = (19524410347656738443 : ℤ) := by
  rw [← strip337_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip337_data_checked.1

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip338_data_checked :
    (frozenSavedStrip338.map FrozenSavedRow.savedQ80).sum = (21193807844330487688 : ℤ) ∧
      frozenSavedStrip338.length = 512 - firstU (⟨12, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip338_sum :
    (∑ j : Fin (512 - firstU (⟨12, by decide⟩ : Fin 186)),
      (frozenSavedStrip338.getD j.val default).savedQ80) = (21193807844330487688 : ℤ) := by
  rw [← strip338_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip338_data_checked.1

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip339_data_checked :
    (frozenSavedStrip339.map FrozenSavedRow.savedQ80).sum = (22839613918301871874 : ℤ) ∧
      frozenSavedStrip339.length = 512 - firstU (⟨13, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip339_sum :
    (∑ j : Fin (512 - firstU (⟨13, by decide⟩ : Fin 186)),
      (frozenSavedStrip339.getD j.val default).savedQ80) = (22839613918301871874 : ℤ) := by
  rw [← strip339_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip339_data_checked.1

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip340_data_checked :
    (frozenSavedStrip340.map FrozenSavedRow.savedQ80).sum = (24470170606658203033 : ℤ) ∧
      frozenSavedStrip340.length = 512 - firstU (⟨14, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip340_sum :
    (∑ j : Fin (512 - firstU (⟨14, by decide⟩ : Fin 186)),
      (frozenSavedStrip340.getD j.val default).savedQ80) = (24470170606658203033 : ℤ) := by
  rw [← strip340_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip340_data_checked.1

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip341_data_checked :
    (frozenSavedStrip341.map FrozenSavedRow.savedQ80).sum = (26076943363443978714 : ℤ) ∧
      frozenSavedStrip341.length = 512 - firstU (⟨15, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip341_sum :
    (∑ j : Fin (512 - firstU (⟨15, by decide⟩ : Fin 186)),
      (frozenSavedStrip341.getD j.val default).savedQ80) = (26076943363443978714 : ℤ) := by
  rw [← strip341_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip341_data_checked.1

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip342_data_checked :
    (frozenSavedStrip342.map FrozenSavedRow.savedQ80).sum = (27668289317813599742 : ℤ) ∧
      frozenSavedStrip342.length = 512 - firstU (⟨16, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip342_sum :
    (∑ j : Fin (512 - firstU (⟨16, by decide⟩ : Fin 186)),
      (frozenSavedStrip342.getD j.val default).savedQ80) = (27668289317813599742 : ℤ) := by
  rw [← strip342_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip342_data_checked.1

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip343_data_checked :
    (frozenSavedStrip343.map FrozenSavedRow.savedQ80).sum = (29235656652776030346 : ℤ) ∧
      frozenSavedStrip343.length = 512 - firstU (⟨17, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip343_sum :
    (∑ j : Fin (512 - firstU (⟨17, by decide⟩ : Fin 186)),
      (frozenSavedStrip343.getD j.val default).savedQ80) = (29235656652776030346 : ℤ) := by
  rw [← strip343_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip343_data_checked.1

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip344_data_checked :
    (frozenSavedStrip344.map FrozenSavedRow.savedQ80).sum = (30787417673562115822 : ℤ) ∧
      frozenSavedStrip344.length = 512 - firstU (⟨18, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip344_sum :
    (∑ j : Fin (512 - firstU (⟨18, by decide⟩ : Fin 186)),
      (frozenSavedStrip344.getD j.val default).savedQ80) = (30787417673562115822 : ℤ) := by
  rw [← strip344_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip344_data_checked.1

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip345_data_checked :
    (frozenSavedStrip345.map FrozenSavedRow.savedQ80).sum = (32315003179272328751 : ℤ) ∧
      frozenSavedStrip345.length = 512 - firstU (⟨19, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip345_sum :
    (∑ j : Fin (512 - firstU (⟨19, by decide⟩ : Fin 186)),
      (frozenSavedStrip345.getD j.val default).savedQ80) = (32315003179272328751 : ℤ) := by
  rw [← strip345_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip345_data_checked.1

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip346_data_checked :
    (frozenSavedStrip346.map FrozenSavedRow.savedQ80).sum = (33831110883130648301 : ℤ) ∧
      frozenSavedStrip346.length = 512 - firstU (⟨20, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip346_sum :
    (∑ j : Fin (512 - firstU (⟨20, by decide⟩ : Fin 186)),
      (frozenSavedStrip346.getD j.val default).savedQ80) = (33831110883130648301 : ℤ) := by
  rw [← strip346_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip346_data_checked.1

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip347_data_checked :
    (frozenSavedStrip347.map FrozenSavedRow.savedQ80).sum = (35327165504524792895 : ℤ) ∧
      frozenSavedStrip347.length = 512 - firstU (⟨21, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip347_sum :
    (∑ j : Fin (512 - firstU (⟨21, by decide⟩ : Fin 186)),
      (frozenSavedStrip347.getD j.val default).savedQ80) = (35327165504524792895 : ℤ) := by
  rw [← strip347_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip347_data_checked.1

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip348_data_checked :
    (frozenSavedStrip348.map FrozenSavedRow.savedQ80).sum = (36798688994084721657 : ℤ) ∧
      frozenSavedStrip348.length = 512 - firstU (⟨22, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip348_sum :
    (∑ j : Fin (512 - firstU (⟨22, by decide⟩ : Fin 186)),
      (frozenSavedStrip348.getD j.val default).savedQ80) = (36798688994084721657 : ℤ) := by
  rw [← strip348_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip348_data_checked.1

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip349_data_checked :
    (frozenSavedStrip349.map FrozenSavedRow.savedQ80).sum = (38254154695126559089 : ℤ) ∧
      frozenSavedStrip349.length = 512 - firstU (⟨23, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip349_sum :
    (∑ j : Fin (512 - firstU (⟨23, by decide⟩ : Fin 186)),
      (frozenSavedStrip349.getD j.val default).savedQ80) = (38254154695126559089 : ℤ) := by
  rw [← strip349_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip349_data_checked.1

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip350_data_checked :
    (frozenSavedStrip350.map FrozenSavedRow.savedQ80).sum = (39689276876346969104 : ℤ) ∧
      frozenSavedStrip350.length = 512 - firstU (⟨24, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip350_sum :
    (∑ j : Fin (512 - firstU (⟨24, by decide⟩ : Fin 186)),
      (frozenSavedStrip350.getD j.val default).savedQ80) = (39689276876346969104 : ℤ) := by
  rw [← strip350_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip350_data_checked.1

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip351_data_checked :
    (frozenSavedStrip351.map FrozenSavedRow.savedQ80).sum = (41103831376704011855 : ℤ) ∧
      frozenSavedStrip351.length = 512 - firstU (⟨25, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip351_sum :
    (∑ j : Fin (512 - firstU (⟨25, by decide⟩ : Fin 186)),
      (frozenSavedStrip351.getD j.val default).savedQ80) = (41103831376704011855 : ℤ) := by
  rw [← strip351_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip351_data_checked.1

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip352_data_checked :
    (frozenSavedStrip352.map FrozenSavedRow.savedQ80).sum = (42497845898009198819 : ℤ) ∧
      frozenSavedStrip352.length = 512 - firstU (⟨26, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip352_sum :
    (∑ j : Fin (512 - firstU (⟨26, by decide⟩ : Fin 186)),
      (frozenSavedStrip352.getD j.val default).savedQ80) = (42497845898009198819 : ℤ) := by
  rw [← strip352_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip352_data_checked.1

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip353_data_checked :
    (frozenSavedStrip353.map FrozenSavedRow.savedQ80).sum = (43871095150916834721 : ℤ) ∧
      frozenSavedStrip353.length = 512 - firstU (⟨27, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip353_sum :
    (∑ j : Fin (512 - firstU (⟨27, by decide⟩ : Fin 186)),
      (frozenSavedStrip353.getD j.val default).savedQ80) = (43871095150916834721 : ℤ) := by
  rw [← strip353_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip353_data_checked.1

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip354_data_checked :
    (frozenSavedStrip354.map FrozenSavedRow.savedQ80).sum = (45223605674689512948 : ℤ) ∧
      frozenSavedStrip354.length = 512 - firstU (⟨28, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip354_sum :
    (∑ j : Fin (512 - firstU (⟨28, by decide⟩ : Fin 186)),
      (frozenSavedStrip354.getD j.val default).savedQ80) = (45223605674689512948 : ℤ) := by
  rw [← strip354_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip354_data_checked.1

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip355_data_checked :
    (frozenSavedStrip355.map FrozenSavedRow.savedQ80).sum = (46563978102258586358 : ℤ) ∧
      frozenSavedStrip355.length = 512 - firstU (⟨29, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip355_sum :
    (∑ j : Fin (512 - firstU (⟨29, by decide⟩ : Fin 186)),
      (frozenSavedStrip355.getD j.val default).savedQ80) = (46563978102258586358 : ℤ) := by
  rw [← strip355_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip355_data_checked.1

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip356_data_checked :
    (frozenSavedStrip356.map FrozenSavedRow.savedQ80).sum = (47879008023534197731 : ℤ) ∧
      frozenSavedStrip356.length = 512 - firstU (⟨30, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip356_sum :
    (∑ j : Fin (512 - firstU (⟨30, by decide⟩ : Fin 186)),
      (frozenSavedStrip356.getD j.val default).savedQ80) = (47879008023534197731 : ℤ) := by
  rw [← strip356_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip356_data_checked.1

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip357_data_checked :
    (frozenSavedStrip357.map FrozenSavedRow.savedQ80).sum = (50944639051949649084 : ℤ) ∧
      frozenSavedStrip357.length = 512 - firstU (⟨31, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip357_sum :
    (∑ j : Fin (512 - firstU (⟨31, by decide⟩ : Fin 186)),
      (frozenSavedStrip357.getD j.val default).savedQ80) = (50944639051949649084 : ℤ) := by
  rw [← strip357_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip357_data_checked.1

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip358_data_checked :
    (frozenSavedStrip358.map FrozenSavedRow.savedQ80).sum = (52213488246889920875 : ℤ) ∧
      frozenSavedStrip358.length = 512 - firstU (⟨32, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip358_sum :
    (∑ j : Fin (512 - firstU (⟨32, by decide⟩ : Fin 186)),
      (frozenSavedStrip358.getD j.val default).savedQ80) = (52213488246889920875 : ℤ) := by
  rw [← strip358_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip358_data_checked.1

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip359_data_checked :
    (frozenSavedStrip359.map FrozenSavedRow.savedQ80).sum = (53465393410309650056 : ℤ) ∧
      frozenSavedStrip359.length = 512 - firstU (⟨33, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip359_sum :
    (∑ j : Fin (512 - firstU (⟨33, by decide⟩ : Fin 186)),
      (frozenSavedStrip359.getD j.val default).savedQ80) = (53465393410309650056 : ℤ) := by
  rw [← strip359_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip359_data_checked.1

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip360_data_checked :
    (frozenSavedStrip360.map FrozenSavedRow.savedQ80).sum = (54691519808168211640 : ℤ) ∧
      frozenSavedStrip360.length = 512 - firstU (⟨34, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip360_sum :
    (∑ j : Fin (512 - firstU (⟨34, by decide⟩ : Fin 186)),
      (frozenSavedStrip360.getD j.val default).savedQ80) = (54691519808168211640 : ℤ) := by
  rw [← strip360_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip360_data_checked.1

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip361_data_checked :
    (frozenSavedStrip361.map FrozenSavedRow.savedQ80).sum = (54144469897406376769 : ℤ) ∧
      frozenSavedStrip361.length = 512 - firstU (⟨35, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip361_sum :
    (∑ j : Fin (512 - firstU (⟨35, by decide⟩ : Fin 186)),
      (frozenSavedStrip361.getD j.val default).savedQ80) = (54144469897406376769 : ℤ) := by
  rw [← strip361_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip361_data_checked.1

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip362_data_checked :
    (frozenSavedStrip362.map FrozenSavedRow.savedQ80).sum = (55331383670759679939 : ℤ) ∧
      frozenSavedStrip362.length = 512 - firstU (⟨36, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip362_sum :
    (∑ j : Fin (512 - firstU (⟨36, by decide⟩ : Fin 186)),
      (frozenSavedStrip362.getD j.val default).savedQ80) = (55331383670759679939 : ℤ) := by
  rw [← strip362_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip362_data_checked.1

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip363_data_checked :
    (frozenSavedStrip363.map FrozenSavedRow.savedQ80).sum = (56501162806005443676 : ℤ) ∧
      frozenSavedStrip363.length = 512 - firstU (⟨37, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip363_sum :
    (∑ j : Fin (512 - firstU (⟨37, by decide⟩ : Fin 186)),
      (frozenSavedStrip363.getD j.val default).savedQ80) = (56501162806005443676 : ℤ) := by
  rw [← strip363_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip363_data_checked.1

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip364_data_checked :
    (frozenSavedStrip364.map FrozenSavedRow.savedQ80).sum = (57653581407710517769 : ℤ) ∧
      frozenSavedStrip364.length = 512 - firstU (⟨38, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip364_sum :
    (∑ j : Fin (512 - firstU (⟨38, by decide⟩ : Fin 186)),
      (frozenSavedStrip364.getD j.val default).savedQ80) = (57653581407710517769 : ℤ) := by
  rw [← strip364_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip364_data_checked.1

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip365_data_checked :
    (frozenSavedStrip365.map FrozenSavedRow.savedQ80).sum = (58779626091048969456 : ℤ) ∧
      frozenSavedStrip365.length = 512 - firstU (⟨39, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip365_sum :
    (∑ j : Fin (512 - firstU (⟨39, by decide⟩ : Fin 186)),
      (frozenSavedStrip365.getD j.val default).savedQ80) = (58779626091048969456 : ℤ) := by
  rw [← strip365_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip365_data_checked.1

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip366_data_checked :
    (frozenSavedStrip366.map FrozenSavedRow.savedQ80).sum = (59888105862971740803 : ℤ) ∧
      frozenSavedStrip366.length = 512 - firstU (⟨40, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip366_sum :
    (∑ j : Fin (512 - firstU (⟨40, by decide⟩ : Fin 186)),
      (frozenSavedStrip366.getD j.val default).savedQ80) = (59888105862971740803 : ℤ) := by
  rw [← strip366_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip366_data_checked.1

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip367_data_checked :
    (frozenSavedStrip367.map FrozenSavedRow.savedQ80).sum = (60969988718923512199 : ℤ) ∧
      frozenSavedStrip367.length = 512 - firstU (⟨41, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip367_sum :
    (∑ j : Fin (512 - firstU (⟨41, by decide⟩ : Fin 186)),
      (frozenSavedStrip367.getD j.val default).savedQ80) = (60969988718923512199 : ℤ) := by
  rw [← strip367_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip367_data_checked.1

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip368_data_checked :
    (frozenSavedStrip368.map FrozenSavedRow.savedQ80).sum = (62034099821223097640 : ℤ) ∧
      frozenSavedStrip368.length = 512 - firstU (⟨42, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip368_sum :
    (∑ j : Fin (512 - firstU (⟨42, by decide⟩ : Fin 186)),
      (frozenSavedStrip368.getD j.val default).savedQ80) = (62034099821223097640 : ℤ) := by
  rw [← strip368_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip368_data_checked.1

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip369_data_checked :
    (frozenSavedStrip369.map FrozenSavedRow.savedQ80).sum = (63071388421801201131 : ℤ) ∧
      frozenSavedStrip369.length = 512 - firstU (⟨43, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip369_sum :
    (∑ j : Fin (512 - firstU (⟨43, by decide⟩ : Fin 186)),
      (frozenSavedStrip369.getD j.val default).savedQ80) = (63071388421801201131 : ℤ) := by
  rw [← strip369_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip369_data_checked.1

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip370_data_checked :
    (frozenSavedStrip370.map FrozenSavedRow.savedQ80).sum = (64090695922670683372 : ℤ) ∧
      frozenSavedStrip370.length = 512 - firstU (⟨44, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip370_sum :
    (∑ j : Fin (512 - firstU (⟨44, by decide⟩ : Fin 186)),
      (frozenSavedStrip370.getD j.val default).savedQ80) = (64090695922670683372 : ℤ) := by
  rw [← strip370_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip370_data_checked.1

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip371_data_checked :
    (frozenSavedStrip371.map FrozenSavedRow.savedQ80).sum = (65087578033171962883 : ℤ) ∧
      frozenSavedStrip371.length = 512 - firstU (⟨45, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip371_sum :
    (∑ j : Fin (512 - firstU (⟨45, by decide⟩ : Fin 186)),
      (frozenSavedStrip371.getD j.val default).savedQ80) = (65087578033171962883 : ℤ) := by
  rw [← strip371_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip371_data_checked.1

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip372_data_checked :
    (frozenSavedStrip372.map FrozenSavedRow.savedQ80).sum = (66066274870622807606 : ℤ) ∧
      frozenSavedStrip372.length = 512 - firstU (⟨46, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip372_sum :
    (∑ j : Fin (512 - firstU (⟨46, by decide⟩ : Fin 186)),
      (frozenSavedStrip372.getD j.val default).savedQ80) = (66066274870622807606 : ℤ) := by
  rw [← strip372_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip372_data_checked.1

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip373_data_checked :
    (frozenSavedStrip373.map FrozenSavedRow.savedQ80).sum = (68730573657360614458 : ℤ) ∧
      frozenSavedStrip373.length = 512 - firstU (⟨47, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip373_sum :
    (∑ j : Fin (512 - firstU (⟨47, by decide⟩ : Fin 186)),
      (frozenSavedStrip373.getD j.val default).savedQ80) = (68730573657360614458 : ℤ) := by
  rw [← strip373_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip373_data_checked.1

end ImbalancedChen.P2HistoricalSavedFloorStoredTotal
