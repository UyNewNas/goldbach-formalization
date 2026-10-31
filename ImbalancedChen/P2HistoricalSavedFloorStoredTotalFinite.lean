import ImbalancedChen.P2HistoricalSavedFloorRowsSourceCore
import ImbalancedChen.P2HistoricalSavedFloorStoredTotalBlock00
import ImbalancedChen.P2HistoricalSavedFloorStoredTotalBlock01
import ImbalancedChen.P2HistoricalSavedFloorStoredTotalBlock02
import ImbalancedChen.P2HistoricalSavedFloorStoredTotalBlock03
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

namespace ImbalancedChen.P2HistoricalSavedFloorStoredTotal
open P2HistoricalSavedFloorRowsBinder
open Certificates.PairedV2 Certificates.PairedV2.FullMask
open scoped BigOperators
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000

def stripTotals : Fin 186 → ℤ :=
  ![1878933774938557092, 3739528744218871846, 5581698956890702623, 7409476840812841656, 9218663137600588279, 11013297164532975245, 12785041168942599196, 14542064496731843928, 16276012586846795368, 16144677483770159531, 17844146246146058095, 19524410347656738443, 21193807844330487688, 22839613918301871874, 24470170606658203033, 26076943363443978714, 27668289317813599742, 29235656652776030346, 30787417673562115822, 32315003179272328751, 33831110883130648301, 35327165504524792895, 36798688994084721657, 38254154695126559089, 39689276876346969104, 41103831376704011855, 42497845898009198819, 43871095150916834721, 45223605674689512948, 46563978102258586358, 47879008023534197731, 50944639051949649084, 52213488246889920875, 53465393410309650056, 54691519808168211640, 54144469897406376769, 55331383670759679939, 56501162806005443676, 57653581407710517769, 58779626091048969456, 59888105862971740803, 60969988718923512199, 62034099821223097640, 63071388421801201131, 64090695922670683372, 65087578033171962883, 66066274870622807606, 68730573657360614458, 69659549808423965617, 70565650980692376976, 71448485752176949282, 72308218203010437747, 73144455565645040761, 73957360544996248851, 74751565813110637222, 75521862352182654260, 76273089807235061936, 76995645160058408767, 77694292635095144023, 78373242476110739512, 79023433627580878777, 79648997356112387936, 80259805286508210672, 80841418120587397881, 81398033645934297398, 81934774451880662403, 82441480990650898779, 82923189166009281916, 83384368079924327771, 83815412517903779375, 84225682550264878197, 84615524751946324938, 84979371042398021998, 85317552928184889405, 85629478096626639455, 85915476485964730747, 86174954156819379282, 86408239450934727921, 86614736786390058099, 86799886935136325727, 86963106676582954897, 87094487367845978527, 87203673733768362643, 87280735709297080998, 87335336112464155650, 87357523317076893350, 87352302922039050555, 87324225932716724075, 87273290574748870723, 87189792320441915685, 87077752669674695507, 86942526320012469073, 86773629558689131546, 86576333578048587719, 86073549771707232374, 85275678961314589222, 84771745342154755244, 83981723015803806364, 84991107686214959059, 84194192127536546198, 83698561772879733678, 82904486630298164318, 82407556237030346695, 81621574612131188336, 81128592209946224693, 80340164537519463007, 79856498834033134735, 79366390579371522657, 78591326480437679246, 78105230003812111201, 77333126050651047902, 76851069656625674046, 76081948989900395482, 75603961278727556492, 74837847289993523072, 74363957162615728162, 73595972201006097751, 73126203939915137756, 72361257279389387879, 71890649738988413013, 71133756030272390612, 70667318489282676937, 69908438631195592511, 69451284993805651089, 68695516346221929061, 68237422810426890939, 68883469484933383860, 68424663538161026688, 67670113878522421193, 67220854706839842056, 66469462980586265387, 66019119627065224251, 65276301337640967992, 64830283812722531061, 64085184421942373509, 63649026188107698584, 63211374834864996327, 62475404898209301638, 62042164686385365196, 61309478719747058462, 60880682256022128268, 60151307059771961839, 59726987303109246651, 60321861211913925951, 58576006461426349305, 57853329054051698032, 57432911856859734391, 56713622011690814446, 57597683441832855952, 56876539116289621026, 56459991174818519650, 55737007254502716862, 55330309942475647433, 54610755033766650292, 54203351264098340894, 53492605474195764124, 53089869617503987213, 52377167532333803412, 51984590185087987492, 51275403728146498594, 50882014589560360901, 50181936800883388301, 49793323120696811151, 50324778442836129942, 49941171188073857715, 49550922453986107242, 48858332213896737686, 48472911677967673485, 47783962802832455194, 47403407790173486680, 46718131218554596898, 46342479463071697558, 45660906474400475204, 45290196114887701249, 44606960657686448424, 44241224414016342930, 43561737102615638743, 43201013882675728606, 42525306911711509668, 42169636042355854200, 41497741968113308085, 42299832350738889492, 41626030631623545566, 41269275258383203157, 40604856012710529037, 40253225100893230709]

/-- Exact original row-family transport, checked independently for strip 326. -/
theorem row_strip326_sum :
    (∑ j : Fin (512 - firstU (⟨0, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨0, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨0, by decide⟩ : Fin 186) := by
  exact strip326_sum

/-- Exact original row-family transport, checked independently for strip 327. -/
theorem row_strip327_sum :
    (∑ j : Fin (512 - firstU (⟨1, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨1, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨1, by decide⟩ : Fin 186) := by
  exact strip327_sum

/-- Exact original row-family transport, checked independently for strip 328. -/
theorem row_strip328_sum :
    (∑ j : Fin (512 - firstU (⟨2, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨2, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨2, by decide⟩ : Fin 186) := by
  exact strip328_sum

/-- Exact original row-family transport, checked independently for strip 329. -/
theorem row_strip329_sum :
    (∑ j : Fin (512 - firstU (⟨3, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨3, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨3, by decide⟩ : Fin 186) := by
  exact strip329_sum

/-- Exact original row-family transport, checked independently for strip 330. -/
theorem row_strip330_sum :
    (∑ j : Fin (512 - firstU (⟨4, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨4, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨4, by decide⟩ : Fin 186) := by
  exact strip330_sum

/-- Exact original row-family transport, checked independently for strip 331. -/
theorem row_strip331_sum :
    (∑ j : Fin (512 - firstU (⟨5, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨5, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨5, by decide⟩ : Fin 186) := by
  exact strip331_sum

/-- Exact original row-family transport, checked independently for strip 332. -/
theorem row_strip332_sum :
    (∑ j : Fin (512 - firstU (⟨6, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨6, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨6, by decide⟩ : Fin 186) := by
  exact strip332_sum

/-- Exact original row-family transport, checked independently for strip 333. -/
theorem row_strip333_sum :
    (∑ j : Fin (512 - firstU (⟨7, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨7, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨7, by decide⟩ : Fin 186) := by
  exact strip333_sum

/-- Exact original row-family transport, checked independently for strip 334. -/
theorem row_strip334_sum :
    (∑ j : Fin (512 - firstU (⟨8, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨8, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨8, by decide⟩ : Fin 186) := by
  exact strip334_sum

/-- Exact original row-family transport, checked independently for strip 335. -/
theorem row_strip335_sum :
    (∑ j : Fin (512 - firstU (⟨9, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨9, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨9, by decide⟩ : Fin 186) := by
  exact strip335_sum

/-- Exact original row-family transport, checked independently for strip 336. -/
theorem row_strip336_sum :
    (∑ j : Fin (512 - firstU (⟨10, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨10, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨10, by decide⟩ : Fin 186) := by
  exact strip336_sum

/-- Exact original row-family transport, checked independently for strip 337. -/
theorem row_strip337_sum :
    (∑ j : Fin (512 - firstU (⟨11, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨11, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨11, by decide⟩ : Fin 186) := by
  exact strip337_sum

/-- Exact original row-family transport, checked independently for strip 338. -/
theorem row_strip338_sum :
    (∑ j : Fin (512 - firstU (⟨12, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨12, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨12, by decide⟩ : Fin 186) := by
  exact strip338_sum

/-- Exact original row-family transport, checked independently for strip 339. -/
theorem row_strip339_sum :
    (∑ j : Fin (512 - firstU (⟨13, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨13, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨13, by decide⟩ : Fin 186) := by
  exact strip339_sum

/-- Exact original row-family transport, checked independently for strip 340. -/
theorem row_strip340_sum :
    (∑ j : Fin (512 - firstU (⟨14, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨14, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨14, by decide⟩ : Fin 186) := by
  exact strip340_sum

/-- Exact original row-family transport, checked independently for strip 341. -/
theorem row_strip341_sum :
    (∑ j : Fin (512 - firstU (⟨15, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨15, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨15, by decide⟩ : Fin 186) := by
  exact strip341_sum

/-- Exact original row-family transport, checked independently for strip 342. -/
theorem row_strip342_sum :
    (∑ j : Fin (512 - firstU (⟨16, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨16, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨16, by decide⟩ : Fin 186) := by
  exact strip342_sum

/-- Exact original row-family transport, checked independently for strip 343. -/
theorem row_strip343_sum :
    (∑ j : Fin (512 - firstU (⟨17, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨17, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨17, by decide⟩ : Fin 186) := by
  exact strip343_sum

/-- Exact original row-family transport, checked independently for strip 344. -/
theorem row_strip344_sum :
    (∑ j : Fin (512 - firstU (⟨18, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨18, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨18, by decide⟩ : Fin 186) := by
  exact strip344_sum

/-- Exact original row-family transport, checked independently for strip 345. -/
theorem row_strip345_sum :
    (∑ j : Fin (512 - firstU (⟨19, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨19, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨19, by decide⟩ : Fin 186) := by
  exact strip345_sum

/-- Exact original row-family transport, checked independently for strip 346. -/
theorem row_strip346_sum :
    (∑ j : Fin (512 - firstU (⟨20, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨20, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨20, by decide⟩ : Fin 186) := by
  exact strip346_sum

/-- Exact original row-family transport, checked independently for strip 347. -/
theorem row_strip347_sum :
    (∑ j : Fin (512 - firstU (⟨21, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨21, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨21, by decide⟩ : Fin 186) := by
  exact strip347_sum

/-- Exact original row-family transport, checked independently for strip 348. -/
theorem row_strip348_sum :
    (∑ j : Fin (512 - firstU (⟨22, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨22, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨22, by decide⟩ : Fin 186) := by
  exact strip348_sum

/-- Exact original row-family transport, checked independently for strip 349. -/
theorem row_strip349_sum :
    (∑ j : Fin (512 - firstU (⟨23, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨23, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨23, by decide⟩ : Fin 186) := by
  exact strip349_sum

/-- Exact original row-family transport, checked independently for strip 350. -/
theorem row_strip350_sum :
    (∑ j : Fin (512 - firstU (⟨24, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨24, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨24, by decide⟩ : Fin 186) := by
  exact strip350_sum

/-- Exact original row-family transport, checked independently for strip 351. -/
theorem row_strip351_sum :
    (∑ j : Fin (512 - firstU (⟨25, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨25, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨25, by decide⟩ : Fin 186) := by
  exact strip351_sum

/-- Exact original row-family transport, checked independently for strip 352. -/
theorem row_strip352_sum :
    (∑ j : Fin (512 - firstU (⟨26, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨26, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨26, by decide⟩ : Fin 186) := by
  exact strip352_sum

/-- Exact original row-family transport, checked independently for strip 353. -/
theorem row_strip353_sum :
    (∑ j : Fin (512 - firstU (⟨27, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨27, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨27, by decide⟩ : Fin 186) := by
  exact strip353_sum

/-- Exact original row-family transport, checked independently for strip 354. -/
theorem row_strip354_sum :
    (∑ j : Fin (512 - firstU (⟨28, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨28, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨28, by decide⟩ : Fin 186) := by
  exact strip354_sum

/-- Exact original row-family transport, checked independently for strip 355. -/
theorem row_strip355_sum :
    (∑ j : Fin (512 - firstU (⟨29, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨29, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨29, by decide⟩ : Fin 186) := by
  exact strip355_sum

/-- Exact original row-family transport, checked independently for strip 356. -/
theorem row_strip356_sum :
    (∑ j : Fin (512 - firstU (⟨30, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨30, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨30, by decide⟩ : Fin 186) := by
  exact strip356_sum

/-- Exact original row-family transport, checked independently for strip 357. -/
theorem row_strip357_sum :
    (∑ j : Fin (512 - firstU (⟨31, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨31, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨31, by decide⟩ : Fin 186) := by
  exact strip357_sum

/-- Exact original row-family transport, checked independently for strip 358. -/
theorem row_strip358_sum :
    (∑ j : Fin (512 - firstU (⟨32, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨32, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨32, by decide⟩ : Fin 186) := by
  exact strip358_sum

/-- Exact original row-family transport, checked independently for strip 359. -/
theorem row_strip359_sum :
    (∑ j : Fin (512 - firstU (⟨33, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨33, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨33, by decide⟩ : Fin 186) := by
  exact strip359_sum

/-- Exact original row-family transport, checked independently for strip 360. -/
theorem row_strip360_sum :
    (∑ j : Fin (512 - firstU (⟨34, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨34, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨34, by decide⟩ : Fin 186) := by
  exact strip360_sum

/-- Exact original row-family transport, checked independently for strip 361. -/
theorem row_strip361_sum :
    (∑ j : Fin (512 - firstU (⟨35, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨35, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨35, by decide⟩ : Fin 186) := by
  exact strip361_sum

/-- Exact original row-family transport, checked independently for strip 362. -/
theorem row_strip362_sum :
    (∑ j : Fin (512 - firstU (⟨36, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨36, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨36, by decide⟩ : Fin 186) := by
  exact strip362_sum

/-- Exact original row-family transport, checked independently for strip 363. -/
theorem row_strip363_sum :
    (∑ j : Fin (512 - firstU (⟨37, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨37, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨37, by decide⟩ : Fin 186) := by
  exact strip363_sum

/-- Exact original row-family transport, checked independently for strip 364. -/
theorem row_strip364_sum :
    (∑ j : Fin (512 - firstU (⟨38, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨38, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨38, by decide⟩ : Fin 186) := by
  exact strip364_sum

/-- Exact original row-family transport, checked independently for strip 365. -/
theorem row_strip365_sum :
    (∑ j : Fin (512 - firstU (⟨39, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨39, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨39, by decide⟩ : Fin 186) := by
  exact strip365_sum

/-- Exact original row-family transport, checked independently for strip 366. -/
theorem row_strip366_sum :
    (∑ j : Fin (512 - firstU (⟨40, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨40, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨40, by decide⟩ : Fin 186) := by
  exact strip366_sum

/-- Exact original row-family transport, checked independently for strip 367. -/
theorem row_strip367_sum :
    (∑ j : Fin (512 - firstU (⟨41, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨41, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨41, by decide⟩ : Fin 186) := by
  exact strip367_sum

/-- Exact original row-family transport, checked independently for strip 368. -/
theorem row_strip368_sum :
    (∑ j : Fin (512 - firstU (⟨42, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨42, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨42, by decide⟩ : Fin 186) := by
  exact strip368_sum

/-- Exact original row-family transport, checked independently for strip 369. -/
theorem row_strip369_sum :
    (∑ j : Fin (512 - firstU (⟨43, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨43, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨43, by decide⟩ : Fin 186) := by
  exact strip369_sum

/-- Exact original row-family transport, checked independently for strip 370. -/
theorem row_strip370_sum :
    (∑ j : Fin (512 - firstU (⟨44, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨44, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨44, by decide⟩ : Fin 186) := by
  exact strip370_sum

/-- Exact original row-family transport, checked independently for strip 371. -/
theorem row_strip371_sum :
    (∑ j : Fin (512 - firstU (⟨45, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨45, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨45, by decide⟩ : Fin 186) := by
  exact strip371_sum

/-- Exact original row-family transport, checked independently for strip 372. -/
theorem row_strip372_sum :
    (∑ j : Fin (512 - firstU (⟨46, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨46, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨46, by decide⟩ : Fin 186) := by
  exact strip372_sum

/-- Exact original row-family transport, checked independently for strip 373. -/
theorem row_strip373_sum :
    (∑ j : Fin (512 - firstU (⟨47, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨47, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨47, by decide⟩ : Fin 186) := by
  exact strip373_sum

/-- Exact original row-family transport, checked independently for strip 374. -/
theorem row_strip374_sum :
    (∑ j : Fin (512 - firstU (⟨48, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨48, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨48, by decide⟩ : Fin 186) := by
  exact strip374_sum

/-- Exact original row-family transport, checked independently for strip 375. -/
theorem row_strip375_sum :
    (∑ j : Fin (512 - firstU (⟨49, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨49, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨49, by decide⟩ : Fin 186) := by
  exact strip375_sum

/-- Exact original row-family transport, checked independently for strip 376. -/
theorem row_strip376_sum :
    (∑ j : Fin (512 - firstU (⟨50, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨50, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨50, by decide⟩ : Fin 186) := by
  exact strip376_sum

/-- Exact original row-family transport, checked independently for strip 377. -/
theorem row_strip377_sum :
    (∑ j : Fin (512 - firstU (⟨51, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨51, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨51, by decide⟩ : Fin 186) := by
  exact strip377_sum

/-- Exact original row-family transport, checked independently for strip 378. -/
theorem row_strip378_sum :
    (∑ j : Fin (512 - firstU (⟨52, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨52, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨52, by decide⟩ : Fin 186) := by
  exact strip378_sum

/-- Exact original row-family transport, checked independently for strip 379. -/
theorem row_strip379_sum :
    (∑ j : Fin (512 - firstU (⟨53, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨53, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨53, by decide⟩ : Fin 186) := by
  exact strip379_sum

/-- Exact original row-family transport, checked independently for strip 380. -/
theorem row_strip380_sum :
    (∑ j : Fin (512 - firstU (⟨54, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨54, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨54, by decide⟩ : Fin 186) := by
  exact strip380_sum

/-- Exact original row-family transport, checked independently for strip 381. -/
theorem row_strip381_sum :
    (∑ j : Fin (512 - firstU (⟨55, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨55, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨55, by decide⟩ : Fin 186) := by
  exact strip381_sum

/-- Exact original row-family transport, checked independently for strip 382. -/
theorem row_strip382_sum :
    (∑ j : Fin (512 - firstU (⟨56, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨56, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨56, by decide⟩ : Fin 186) := by
  exact strip382_sum

/-- Exact original row-family transport, checked independently for strip 383. -/
theorem row_strip383_sum :
    (∑ j : Fin (512 - firstU (⟨57, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨57, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨57, by decide⟩ : Fin 186) := by
  exact strip383_sum

/-- Exact original row-family transport, checked independently for strip 384. -/
theorem row_strip384_sum :
    (∑ j : Fin (512 - firstU (⟨58, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨58, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨58, by decide⟩ : Fin 186) := by
  exact strip384_sum

/-- Exact original row-family transport, checked independently for strip 385. -/
theorem row_strip385_sum :
    (∑ j : Fin (512 - firstU (⟨59, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨59, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨59, by decide⟩ : Fin 186) := by
  exact strip385_sum

/-- Exact original row-family transport, checked independently for strip 386. -/
theorem row_strip386_sum :
    (∑ j : Fin (512 - firstU (⟨60, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨60, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨60, by decide⟩ : Fin 186) := by
  exact strip386_sum

/-- Exact original row-family transport, checked independently for strip 387. -/
theorem row_strip387_sum :
    (∑ j : Fin (512 - firstU (⟨61, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨61, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨61, by decide⟩ : Fin 186) := by
  exact strip387_sum

/-- Exact original row-family transport, checked independently for strip 388. -/
theorem row_strip388_sum :
    (∑ j : Fin (512 - firstU (⟨62, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨62, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨62, by decide⟩ : Fin 186) := by
  exact strip388_sum

/-- Exact original row-family transport, checked independently for strip 389. -/
theorem row_strip389_sum :
    (∑ j : Fin (512 - firstU (⟨63, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨63, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨63, by decide⟩ : Fin 186) := by
  exact strip389_sum

/-- Exact original row-family transport, checked independently for strip 390. -/
theorem row_strip390_sum :
    (∑ j : Fin (512 - firstU (⟨64, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨64, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨64, by decide⟩ : Fin 186) := by
  exact strip390_sum

/-- Exact original row-family transport, checked independently for strip 391. -/
theorem row_strip391_sum :
    (∑ j : Fin (512 - firstU (⟨65, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨65, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨65, by decide⟩ : Fin 186) := by
  exact strip391_sum

/-- Exact original row-family transport, checked independently for strip 392. -/
theorem row_strip392_sum :
    (∑ j : Fin (512 - firstU (⟨66, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨66, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨66, by decide⟩ : Fin 186) := by
  exact strip392_sum

/-- Exact original row-family transport, checked independently for strip 393. -/
theorem row_strip393_sum :
    (∑ j : Fin (512 - firstU (⟨67, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨67, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨67, by decide⟩ : Fin 186) := by
  exact strip393_sum

/-- Exact original row-family transport, checked independently for strip 394. -/
theorem row_strip394_sum :
    (∑ j : Fin (512 - firstU (⟨68, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨68, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨68, by decide⟩ : Fin 186) := by
  exact strip394_sum

/-- Exact original row-family transport, checked independently for strip 395. -/
theorem row_strip395_sum :
    (∑ j : Fin (512 - firstU (⟨69, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨69, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨69, by decide⟩ : Fin 186) := by
  exact strip395_sum

/-- Exact original row-family transport, checked independently for strip 396. -/
theorem row_strip396_sum :
    (∑ j : Fin (512 - firstU (⟨70, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨70, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨70, by decide⟩ : Fin 186) := by
  exact strip396_sum

/-- Exact original row-family transport, checked independently for strip 397. -/
theorem row_strip397_sum :
    (∑ j : Fin (512 - firstU (⟨71, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨71, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨71, by decide⟩ : Fin 186) := by
  exact strip397_sum

/-- Exact original row-family transport, checked independently for strip 398. -/
theorem row_strip398_sum :
    (∑ j : Fin (512 - firstU (⟨72, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨72, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨72, by decide⟩ : Fin 186) := by
  exact strip398_sum

/-- Exact original row-family transport, checked independently for strip 399. -/
theorem row_strip399_sum :
    (∑ j : Fin (512 - firstU (⟨73, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨73, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨73, by decide⟩ : Fin 186) := by
  exact strip399_sum

/-- Exact original row-family transport, checked independently for strip 400. -/
theorem row_strip400_sum :
    (∑ j : Fin (512 - firstU (⟨74, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨74, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨74, by decide⟩ : Fin 186) := by
  exact strip400_sum

/-- Exact original row-family transport, checked independently for strip 401. -/
theorem row_strip401_sum :
    (∑ j : Fin (512 - firstU (⟨75, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨75, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨75, by decide⟩ : Fin 186) := by
  exact strip401_sum

/-- Exact original row-family transport, checked independently for strip 402. -/
theorem row_strip402_sum :
    (∑ j : Fin (512 - firstU (⟨76, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨76, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨76, by decide⟩ : Fin 186) := by
  exact strip402_sum

/-- Exact original row-family transport, checked independently for strip 403. -/
theorem row_strip403_sum :
    (∑ j : Fin (512 - firstU (⟨77, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨77, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨77, by decide⟩ : Fin 186) := by
  exact strip403_sum

/-- Exact original row-family transport, checked independently for strip 404. -/
theorem row_strip404_sum :
    (∑ j : Fin (512 - firstU (⟨78, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨78, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨78, by decide⟩ : Fin 186) := by
  exact strip404_sum

/-- Exact original row-family transport, checked independently for strip 405. -/
theorem row_strip405_sum :
    (∑ j : Fin (512 - firstU (⟨79, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨79, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨79, by decide⟩ : Fin 186) := by
  exact strip405_sum

/-- Exact original row-family transport, checked independently for strip 406. -/
theorem row_strip406_sum :
    (∑ j : Fin (512 - firstU (⟨80, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨80, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨80, by decide⟩ : Fin 186) := by
  exact strip406_sum

/-- Exact original row-family transport, checked independently for strip 407. -/
theorem row_strip407_sum :
    (∑ j : Fin (512 - firstU (⟨81, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨81, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨81, by decide⟩ : Fin 186) := by
  exact strip407_sum

/-- Exact original row-family transport, checked independently for strip 408. -/
theorem row_strip408_sum :
    (∑ j : Fin (512 - firstU (⟨82, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨82, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨82, by decide⟩ : Fin 186) := by
  exact strip408_sum

/-- Exact original row-family transport, checked independently for strip 409. -/
theorem row_strip409_sum :
    (∑ j : Fin (512 - firstU (⟨83, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨83, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨83, by decide⟩ : Fin 186) := by
  exact strip409_sum

/-- Exact original row-family transport, checked independently for strip 410. -/
theorem row_strip410_sum :
    (∑ j : Fin (512 - firstU (⟨84, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨84, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨84, by decide⟩ : Fin 186) := by
  exact strip410_sum

/-- Exact original row-family transport, checked independently for strip 411. -/
theorem row_strip411_sum :
    (∑ j : Fin (512 - firstU (⟨85, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨85, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨85, by decide⟩ : Fin 186) := by
  exact strip411_sum

/-- Exact original row-family transport, checked independently for strip 412. -/
theorem row_strip412_sum :
    (∑ j : Fin (512 - firstU (⟨86, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨86, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨86, by decide⟩ : Fin 186) := by
  exact strip412_sum

/-- Exact original row-family transport, checked independently for strip 413. -/
theorem row_strip413_sum :
    (∑ j : Fin (512 - firstU (⟨87, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨87, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨87, by decide⟩ : Fin 186) := by
  exact strip413_sum

/-- Exact original row-family transport, checked independently for strip 414. -/
theorem row_strip414_sum :
    (∑ j : Fin (512 - firstU (⟨88, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨88, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨88, by decide⟩ : Fin 186) := by
  exact strip414_sum

/-- Exact original row-family transport, checked independently for strip 415. -/
theorem row_strip415_sum :
    (∑ j : Fin (512 - firstU (⟨89, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨89, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨89, by decide⟩ : Fin 186) := by
  exact strip415_sum

/-- Exact original row-family transport, checked independently for strip 416. -/
theorem row_strip416_sum :
    (∑ j : Fin (512 - firstU (⟨90, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨90, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨90, by decide⟩ : Fin 186) := by
  exact strip416_sum

/-- Exact original row-family transport, checked independently for strip 417. -/
theorem row_strip417_sum :
    (∑ j : Fin (512 - firstU (⟨91, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨91, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨91, by decide⟩ : Fin 186) := by
  exact strip417_sum

/-- Exact original row-family transport, checked independently for strip 418. -/
theorem row_strip418_sum :
    (∑ j : Fin (512 - firstU (⟨92, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨92, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨92, by decide⟩ : Fin 186) := by
  exact strip418_sum

/-- Exact original row-family transport, checked independently for strip 419. -/
theorem row_strip419_sum :
    (∑ j : Fin (512 - firstU (⟨93, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨93, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨93, by decide⟩ : Fin 186) := by
  exact strip419_sum

/-- Exact original row-family transport, checked independently for strip 420. -/
theorem row_strip420_sum :
    (∑ j : Fin (512 - firstU (⟨94, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨94, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨94, by decide⟩ : Fin 186) := by
  exact strip420_sum

/-- Exact original row-family transport, checked independently for strip 421. -/
theorem row_strip421_sum :
    (∑ j : Fin (512 - firstU (⟨95, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨95, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨95, by decide⟩ : Fin 186) := by
  exact strip421_sum

/-- Exact original row-family transport, checked independently for strip 422. -/
theorem row_strip422_sum :
    (∑ j : Fin (512 - firstU (⟨96, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨96, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨96, by decide⟩ : Fin 186) := by
  exact strip422_sum

/-- Exact original row-family transport, checked independently for strip 423. -/
theorem row_strip423_sum :
    (∑ j : Fin (512 - firstU (⟨97, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨97, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨97, by decide⟩ : Fin 186) := by
  exact strip423_sum

/-- Exact original row-family transport, checked independently for strip 424. -/
theorem row_strip424_sum :
    (∑ j : Fin (512 - firstU (⟨98, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨98, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨98, by decide⟩ : Fin 186) := by
  exact strip424_sum

/-- Exact original row-family transport, checked independently for strip 425. -/
theorem row_strip425_sum :
    (∑ j : Fin (512 - firstU (⟨99, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨99, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨99, by decide⟩ : Fin 186) := by
  exact strip425_sum

/-- Exact original row-family transport, checked independently for strip 426. -/
theorem row_strip426_sum :
    (∑ j : Fin (512 - firstU (⟨100, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨100, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨100, by decide⟩ : Fin 186) := by
  exact strip426_sum

/-- Exact original row-family transport, checked independently for strip 427. -/
theorem row_strip427_sum :
    (∑ j : Fin (512 - firstU (⟨101, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨101, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨101, by decide⟩ : Fin 186) := by
  exact strip427_sum

/-- Exact original row-family transport, checked independently for strip 428. -/
theorem row_strip428_sum :
    (∑ j : Fin (512 - firstU (⟨102, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨102, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨102, by decide⟩ : Fin 186) := by
  exact strip428_sum

/-- Exact original row-family transport, checked independently for strip 429. -/
theorem row_strip429_sum :
    (∑ j : Fin (512 - firstU (⟨103, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨103, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨103, by decide⟩ : Fin 186) := by
  exact strip429_sum

/-- Exact original row-family transport, checked independently for strip 430. -/
theorem row_strip430_sum :
    (∑ j : Fin (512 - firstU (⟨104, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨104, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨104, by decide⟩ : Fin 186) := by
  exact strip430_sum

/-- Exact original row-family transport, checked independently for strip 431. -/
theorem row_strip431_sum :
    (∑ j : Fin (512 - firstU (⟨105, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨105, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨105, by decide⟩ : Fin 186) := by
  exact strip431_sum

/-- Exact original row-family transport, checked independently for strip 432. -/
theorem row_strip432_sum :
    (∑ j : Fin (512 - firstU (⟨106, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨106, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨106, by decide⟩ : Fin 186) := by
  exact strip432_sum

/-- Exact original row-family transport, checked independently for strip 433. -/
theorem row_strip433_sum :
    (∑ j : Fin (512 - firstU (⟨107, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨107, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨107, by decide⟩ : Fin 186) := by
  exact strip433_sum

/-- Exact original row-family transport, checked independently for strip 434. -/
theorem row_strip434_sum :
    (∑ j : Fin (512 - firstU (⟨108, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨108, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨108, by decide⟩ : Fin 186) := by
  exact strip434_sum

/-- Exact original row-family transport, checked independently for strip 435. -/
theorem row_strip435_sum :
    (∑ j : Fin (512 - firstU (⟨109, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨109, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨109, by decide⟩ : Fin 186) := by
  exact strip435_sum

/-- Exact original row-family transport, checked independently for strip 436. -/
theorem row_strip436_sum :
    (∑ j : Fin (512 - firstU (⟨110, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨110, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨110, by decide⟩ : Fin 186) := by
  exact strip436_sum

/-- Exact original row-family transport, checked independently for strip 437. -/
theorem row_strip437_sum :
    (∑ j : Fin (512 - firstU (⟨111, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨111, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨111, by decide⟩ : Fin 186) := by
  exact strip437_sum

/-- Exact original row-family transport, checked independently for strip 438. -/
theorem row_strip438_sum :
    (∑ j : Fin (512 - firstU (⟨112, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨112, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨112, by decide⟩ : Fin 186) := by
  exact strip438_sum

/-- Exact original row-family transport, checked independently for strip 439. -/
theorem row_strip439_sum :
    (∑ j : Fin (512 - firstU (⟨113, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨113, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨113, by decide⟩ : Fin 186) := by
  exact strip439_sum

/-- Exact original row-family transport, checked independently for strip 440. -/
theorem row_strip440_sum :
    (∑ j : Fin (512 - firstU (⟨114, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨114, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨114, by decide⟩ : Fin 186) := by
  exact strip440_sum

/-- Exact original row-family transport, checked independently for strip 441. -/
theorem row_strip441_sum :
    (∑ j : Fin (512 - firstU (⟨115, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨115, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨115, by decide⟩ : Fin 186) := by
  exact strip441_sum

/-- Exact original row-family transport, checked independently for strip 442. -/
theorem row_strip442_sum :
    (∑ j : Fin (512 - firstU (⟨116, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨116, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨116, by decide⟩ : Fin 186) := by
  exact strip442_sum

/-- Exact original row-family transport, checked independently for strip 443. -/
theorem row_strip443_sum :
    (∑ j : Fin (512 - firstU (⟨117, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨117, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨117, by decide⟩ : Fin 186) := by
  exact strip443_sum

/-- Exact original row-family transport, checked independently for strip 444. -/
theorem row_strip444_sum :
    (∑ j : Fin (512 - firstU (⟨118, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨118, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨118, by decide⟩ : Fin 186) := by
  exact strip444_sum

/-- Exact original row-family transport, checked independently for strip 445. -/
theorem row_strip445_sum :
    (∑ j : Fin (512 - firstU (⟨119, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨119, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨119, by decide⟩ : Fin 186) := by
  exact strip445_sum

/-- Exact original row-family transport, checked independently for strip 446. -/
theorem row_strip446_sum :
    (∑ j : Fin (512 - firstU (⟨120, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨120, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨120, by decide⟩ : Fin 186) := by
  exact strip446_sum

/-- Exact original row-family transport, checked independently for strip 447. -/
theorem row_strip447_sum :
    (∑ j : Fin (512 - firstU (⟨121, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨121, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨121, by decide⟩ : Fin 186) := by
  exact strip447_sum

/-- Exact original row-family transport, checked independently for strip 448. -/
theorem row_strip448_sum :
    (∑ j : Fin (512 - firstU (⟨122, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨122, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨122, by decide⟩ : Fin 186) := by
  exact strip448_sum

/-- Exact original row-family transport, checked independently for strip 449. -/
theorem row_strip449_sum :
    (∑ j : Fin (512 - firstU (⟨123, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨123, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨123, by decide⟩ : Fin 186) := by
  exact strip449_sum

/-- Exact original row-family transport, checked independently for strip 450. -/
theorem row_strip450_sum :
    (∑ j : Fin (512 - firstU (⟨124, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨124, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨124, by decide⟩ : Fin 186) := by
  exact strip450_sum

/-- Exact original row-family transport, checked independently for strip 451. -/
theorem row_strip451_sum :
    (∑ j : Fin (512 - firstU (⟨125, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨125, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨125, by decide⟩ : Fin 186) := by
  exact strip451_sum

/-- Exact original row-family transport, checked independently for strip 452. -/
theorem row_strip452_sum :
    (∑ j : Fin (512 - firstU (⟨126, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨126, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨126, by decide⟩ : Fin 186) := by
  exact strip452_sum

/-- Exact original row-family transport, checked independently for strip 453. -/
theorem row_strip453_sum :
    (∑ j : Fin (512 - firstU (⟨127, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨127, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨127, by decide⟩ : Fin 186) := by
  exact strip453_sum

/-- Exact original row-family transport, checked independently for strip 454. -/
theorem row_strip454_sum :
    (∑ j : Fin (512 - firstU (⟨128, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨128, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨128, by decide⟩ : Fin 186) := by
  exact strip454_sum

/-- Exact original row-family transport, checked independently for strip 455. -/
theorem row_strip455_sum :
    (∑ j : Fin (512 - firstU (⟨129, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨129, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨129, by decide⟩ : Fin 186) := by
  exact strip455_sum

/-- Exact original row-family transport, checked independently for strip 456. -/
theorem row_strip456_sum :
    (∑ j : Fin (512 - firstU (⟨130, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨130, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨130, by decide⟩ : Fin 186) := by
  exact strip456_sum

/-- Exact original row-family transport, checked independently for strip 457. -/
theorem row_strip457_sum :
    (∑ j : Fin (512 - firstU (⟨131, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨131, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨131, by decide⟩ : Fin 186) := by
  exact strip457_sum

/-- Exact original row-family transport, checked independently for strip 458. -/
theorem row_strip458_sum :
    (∑ j : Fin (512 - firstU (⟨132, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨132, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨132, by decide⟩ : Fin 186) := by
  exact strip458_sum

/-- Exact original row-family transport, checked independently for strip 459. -/
theorem row_strip459_sum :
    (∑ j : Fin (512 - firstU (⟨133, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨133, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨133, by decide⟩ : Fin 186) := by
  exact strip459_sum

/-- Exact original row-family transport, checked independently for strip 460. -/
theorem row_strip460_sum :
    (∑ j : Fin (512 - firstU (⟨134, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨134, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨134, by decide⟩ : Fin 186) := by
  exact strip460_sum

/-- Exact original row-family transport, checked independently for strip 461. -/
theorem row_strip461_sum :
    (∑ j : Fin (512 - firstU (⟨135, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨135, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨135, by decide⟩ : Fin 186) := by
  exact strip461_sum

/-- Exact original row-family transport, checked independently for strip 462. -/
theorem row_strip462_sum :
    (∑ j : Fin (512 - firstU (⟨136, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨136, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨136, by decide⟩ : Fin 186) := by
  exact strip462_sum

/-- Exact original row-family transport, checked independently for strip 463. -/
theorem row_strip463_sum :
    (∑ j : Fin (512 - firstU (⟨137, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨137, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨137, by decide⟩ : Fin 186) := by
  exact strip463_sum

/-- Exact original row-family transport, checked independently for strip 464. -/
theorem row_strip464_sum :
    (∑ j : Fin (512 - firstU (⟨138, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨138, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨138, by decide⟩ : Fin 186) := by
  exact strip464_sum

/-- Exact original row-family transport, checked independently for strip 465. -/
theorem row_strip465_sum :
    (∑ j : Fin (512 - firstU (⟨139, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨139, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨139, by decide⟩ : Fin 186) := by
  exact strip465_sum

/-- Exact original row-family transport, checked independently for strip 466. -/
theorem row_strip466_sum :
    (∑ j : Fin (512 - firstU (⟨140, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨140, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨140, by decide⟩ : Fin 186) := by
  exact strip466_sum

/-- Exact original row-family transport, checked independently for strip 467. -/
theorem row_strip467_sum :
    (∑ j : Fin (512 - firstU (⟨141, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨141, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨141, by decide⟩ : Fin 186) := by
  exact strip467_sum

/-- Exact original row-family transport, checked independently for strip 468. -/
theorem row_strip468_sum :
    (∑ j : Fin (512 - firstU (⟨142, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨142, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨142, by decide⟩ : Fin 186) := by
  exact strip468_sum

/-- Exact original row-family transport, checked independently for strip 469. -/
theorem row_strip469_sum :
    (∑ j : Fin (512 - firstU (⟨143, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨143, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨143, by decide⟩ : Fin 186) := by
  exact strip469_sum

/-- Exact original row-family transport, checked independently for strip 470. -/
theorem row_strip470_sum :
    (∑ j : Fin (512 - firstU (⟨144, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨144, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨144, by decide⟩ : Fin 186) := by
  exact strip470_sum

/-- Exact original row-family transport, checked independently for strip 471. -/
theorem row_strip471_sum :
    (∑ j : Fin (512 - firstU (⟨145, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨145, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨145, by decide⟩ : Fin 186) := by
  exact strip471_sum

/-- Exact original row-family transport, checked independently for strip 472. -/
theorem row_strip472_sum :
    (∑ j : Fin (512 - firstU (⟨146, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨146, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨146, by decide⟩ : Fin 186) := by
  exact strip472_sum

/-- Exact original row-family transport, checked independently for strip 473. -/
theorem row_strip473_sum :
    (∑ j : Fin (512 - firstU (⟨147, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨147, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨147, by decide⟩ : Fin 186) := by
  exact strip473_sum

/-- Exact original row-family transport, checked independently for strip 474. -/
theorem row_strip474_sum :
    (∑ j : Fin (512 - firstU (⟨148, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨148, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨148, by decide⟩ : Fin 186) := by
  exact strip474_sum

/-- Exact original row-family transport, checked independently for strip 475. -/
theorem row_strip475_sum :
    (∑ j : Fin (512 - firstU (⟨149, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨149, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨149, by decide⟩ : Fin 186) := by
  exact strip475_sum

/-- Exact original row-family transport, checked independently for strip 476. -/
theorem row_strip476_sum :
    (∑ j : Fin (512 - firstU (⟨150, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨150, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨150, by decide⟩ : Fin 186) := by
  exact strip476_sum

/-- Exact original row-family transport, checked independently for strip 477. -/
theorem row_strip477_sum :
    (∑ j : Fin (512 - firstU (⟨151, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨151, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨151, by decide⟩ : Fin 186) := by
  exact strip477_sum

/-- Exact original row-family transport, checked independently for strip 478. -/
theorem row_strip478_sum :
    (∑ j : Fin (512 - firstU (⟨152, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨152, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨152, by decide⟩ : Fin 186) := by
  exact strip478_sum

/-- Exact original row-family transport, checked independently for strip 479. -/
theorem row_strip479_sum :
    (∑ j : Fin (512 - firstU (⟨153, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨153, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨153, by decide⟩ : Fin 186) := by
  exact strip479_sum

/-- Exact original row-family transport, checked independently for strip 480. -/
theorem row_strip480_sum :
    (∑ j : Fin (512 - firstU (⟨154, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨154, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨154, by decide⟩ : Fin 186) := by
  exact strip480_sum

/-- Exact original row-family transport, checked independently for strip 481. -/
theorem row_strip481_sum :
    (∑ j : Fin (512 - firstU (⟨155, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨155, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨155, by decide⟩ : Fin 186) := by
  exact strip481_sum

/-- Exact original row-family transport, checked independently for strip 482. -/
theorem row_strip482_sum :
    (∑ j : Fin (512 - firstU (⟨156, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨156, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨156, by decide⟩ : Fin 186) := by
  exact strip482_sum

/-- Exact original row-family transport, checked independently for strip 483. -/
theorem row_strip483_sum :
    (∑ j : Fin (512 - firstU (⟨157, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨157, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨157, by decide⟩ : Fin 186) := by
  exact strip483_sum

/-- Exact original row-family transport, checked independently for strip 484. -/
theorem row_strip484_sum :
    (∑ j : Fin (512 - firstU (⟨158, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨158, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨158, by decide⟩ : Fin 186) := by
  exact strip484_sum

/-- Exact original row-family transport, checked independently for strip 485. -/
theorem row_strip485_sum :
    (∑ j : Fin (512 - firstU (⟨159, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨159, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨159, by decide⟩ : Fin 186) := by
  exact strip485_sum

/-- Exact original row-family transport, checked independently for strip 486. -/
theorem row_strip486_sum :
    (∑ j : Fin (512 - firstU (⟨160, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨160, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨160, by decide⟩ : Fin 186) := by
  exact strip486_sum

/-- Exact original row-family transport, checked independently for strip 487. -/
theorem row_strip487_sum :
    (∑ j : Fin (512 - firstU (⟨161, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨161, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨161, by decide⟩ : Fin 186) := by
  exact strip487_sum

/-- Exact original row-family transport, checked independently for strip 488. -/
theorem row_strip488_sum :
    (∑ j : Fin (512 - firstU (⟨162, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨162, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨162, by decide⟩ : Fin 186) := by
  exact strip488_sum

/-- Exact original row-family transport, checked independently for strip 489. -/
theorem row_strip489_sum :
    (∑ j : Fin (512 - firstU (⟨163, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨163, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨163, by decide⟩ : Fin 186) := by
  exact strip489_sum

/-- Exact original row-family transport, checked independently for strip 490. -/
theorem row_strip490_sum :
    (∑ j : Fin (512 - firstU (⟨164, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨164, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨164, by decide⟩ : Fin 186) := by
  exact strip490_sum

/-- Exact original row-family transport, checked independently for strip 491. -/
theorem row_strip491_sum :
    (∑ j : Fin (512 - firstU (⟨165, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨165, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨165, by decide⟩ : Fin 186) := by
  exact strip491_sum

/-- Exact original row-family transport, checked independently for strip 492. -/
theorem row_strip492_sum :
    (∑ j : Fin (512 - firstU (⟨166, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨166, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨166, by decide⟩ : Fin 186) := by
  exact strip492_sum

/-- Exact original row-family transport, checked independently for strip 493. -/
theorem row_strip493_sum :
    (∑ j : Fin (512 - firstU (⟨167, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨167, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨167, by decide⟩ : Fin 186) := by
  exact strip493_sum

/-- Exact original row-family transport, checked independently for strip 494. -/
theorem row_strip494_sum :
    (∑ j : Fin (512 - firstU (⟨168, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨168, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨168, by decide⟩ : Fin 186) := by
  exact strip494_sum

/-- Exact original row-family transport, checked independently for strip 495. -/
theorem row_strip495_sum :
    (∑ j : Fin (512 - firstU (⟨169, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨169, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨169, by decide⟩ : Fin 186) := by
  exact strip495_sum

/-- Exact original row-family transport, checked independently for strip 496. -/
theorem row_strip496_sum :
    (∑ j : Fin (512 - firstU (⟨170, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨170, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨170, by decide⟩ : Fin 186) := by
  exact strip496_sum

/-- Exact original row-family transport, checked independently for strip 497. -/
theorem row_strip497_sum :
    (∑ j : Fin (512 - firstU (⟨171, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨171, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨171, by decide⟩ : Fin 186) := by
  exact strip497_sum

/-- Exact original row-family transport, checked independently for strip 498. -/
theorem row_strip498_sum :
    (∑ j : Fin (512 - firstU (⟨172, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨172, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨172, by decide⟩ : Fin 186) := by
  exact strip498_sum

/-- Exact original row-family transport, checked independently for strip 499. -/
theorem row_strip499_sum :
    (∑ j : Fin (512 - firstU (⟨173, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨173, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨173, by decide⟩ : Fin 186) := by
  exact strip499_sum

/-- Exact original row-family transport, checked independently for strip 500. -/
theorem row_strip500_sum :
    (∑ j : Fin (512 - firstU (⟨174, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨174, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨174, by decide⟩ : Fin 186) := by
  exact strip500_sum

/-- Exact original row-family transport, checked independently for strip 501. -/
theorem row_strip501_sum :
    (∑ j : Fin (512 - firstU (⟨175, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨175, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨175, by decide⟩ : Fin 186) := by
  exact strip501_sum

/-- Exact original row-family transport, checked independently for strip 502. -/
theorem row_strip502_sum :
    (∑ j : Fin (512 - firstU (⟨176, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨176, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨176, by decide⟩ : Fin 186) := by
  exact strip502_sum

/-- Exact original row-family transport, checked independently for strip 503. -/
theorem row_strip503_sum :
    (∑ j : Fin (512 - firstU (⟨177, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨177, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨177, by decide⟩ : Fin 186) := by
  exact strip503_sum

/-- Exact original row-family transport, checked independently for strip 504. -/
theorem row_strip504_sum :
    (∑ j : Fin (512 - firstU (⟨178, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨178, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨178, by decide⟩ : Fin 186) := by
  exact strip504_sum

/-- Exact original row-family transport, checked independently for strip 505. -/
theorem row_strip505_sum :
    (∑ j : Fin (512 - firstU (⟨179, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨179, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨179, by decide⟩ : Fin 186) := by
  exact strip505_sum

/-- Exact original row-family transport, checked independently for strip 506. -/
theorem row_strip506_sum :
    (∑ j : Fin (512 - firstU (⟨180, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨180, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨180, by decide⟩ : Fin 186) := by
  exact strip506_sum

/-- Exact original row-family transport, checked independently for strip 507. -/
theorem row_strip507_sum :
    (∑ j : Fin (512 - firstU (⟨181, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨181, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨181, by decide⟩ : Fin 186) := by
  exact strip507_sum

/-- Exact original row-family transport, checked independently for strip 508. -/
theorem row_strip508_sum :
    (∑ j : Fin (512 - firstU (⟨182, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨182, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨182, by decide⟩ : Fin 186) := by
  exact strip508_sum

/-- Exact original row-family transport, checked independently for strip 509. -/
theorem row_strip509_sum :
    (∑ j : Fin (512 - firstU (⟨183, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨183, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨183, by decide⟩ : Fin 186) := by
  exact strip509_sum

/-- Exact original row-family transport, checked independently for strip 510. -/
theorem row_strip510_sum :
    (∑ j : Fin (512 - firstU (⟨184, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨184, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨184, by decide⟩ : Fin 186) := by
  exact strip510_sum

/-- Exact original row-family transport, checked independently for strip 511. -/
theorem row_strip511_sum :
    (∑ j : Fin (512 - firstU (⟨185, by decide⟩ : Fin 186)),
      (frozenSavedRow (⟨(⟨185, by decide⟩ : Fin 186), j⟩ : Row)).savedQ80) =
      stripTotals (⟨185, by decide⟩ : Fin 186) := by
  exact strip511_sum

theorem all_strip_sums : ∀ i : Fin 186,
    (∑ j : Fin (512 - firstU i), (frozenSavedRow (⟨i, j⟩ : Row)).savedQ80) =
      stripTotals i := by
  intro i
  fin_cases i
  · exact row_strip326_sum
  · exact row_strip327_sum
  · exact row_strip328_sum
  · exact row_strip329_sum
  · exact row_strip330_sum
  · exact row_strip331_sum
  · exact row_strip332_sum
  · exact row_strip333_sum
  · exact row_strip334_sum
  · exact row_strip335_sum
  · exact row_strip336_sum
  · exact row_strip337_sum
  · exact row_strip338_sum
  · exact row_strip339_sum
  · exact row_strip340_sum
  · exact row_strip341_sum
  · exact row_strip342_sum
  · exact row_strip343_sum
  · exact row_strip344_sum
  · exact row_strip345_sum
  · exact row_strip346_sum
  · exact row_strip347_sum
  · exact row_strip348_sum
  · exact row_strip349_sum
  · exact row_strip350_sum
  · exact row_strip351_sum
  · exact row_strip352_sum
  · exact row_strip353_sum
  · exact row_strip354_sum
  · exact row_strip355_sum
  · exact row_strip356_sum
  · exact row_strip357_sum
  · exact row_strip358_sum
  · exact row_strip359_sum
  · exact row_strip360_sum
  · exact row_strip361_sum
  · exact row_strip362_sum
  · exact row_strip363_sum
  · exact row_strip364_sum
  · exact row_strip365_sum
  · exact row_strip366_sum
  · exact row_strip367_sum
  · exact row_strip368_sum
  · exact row_strip369_sum
  · exact row_strip370_sum
  · exact row_strip371_sum
  · exact row_strip372_sum
  · exact row_strip373_sum
  · exact row_strip374_sum
  · exact row_strip375_sum
  · exact row_strip376_sum
  · exact row_strip377_sum
  · exact row_strip378_sum
  · exact row_strip379_sum
  · exact row_strip380_sum
  · exact row_strip381_sum
  · exact row_strip382_sum
  · exact row_strip383_sum
  · exact row_strip384_sum
  · exact row_strip385_sum
  · exact row_strip386_sum
  · exact row_strip387_sum
  · exact row_strip388_sum
  · exact row_strip389_sum
  · exact row_strip390_sum
  · exact row_strip391_sum
  · exact row_strip392_sum
  · exact row_strip393_sum
  · exact row_strip394_sum
  · exact row_strip395_sum
  · exact row_strip396_sum
  · exact row_strip397_sum
  · exact row_strip398_sum
  · exact row_strip399_sum
  · exact row_strip400_sum
  · exact row_strip401_sum
  · exact row_strip402_sum
  · exact row_strip403_sum
  · exact row_strip404_sum
  · exact row_strip405_sum
  · exact row_strip406_sum
  · exact row_strip407_sum
  · exact row_strip408_sum
  · exact row_strip409_sum
  · exact row_strip410_sum
  · exact row_strip411_sum
  · exact row_strip412_sum
  · exact row_strip413_sum
  · exact row_strip414_sum
  · exact row_strip415_sum
  · exact row_strip416_sum
  · exact row_strip417_sum
  · exact row_strip418_sum
  · exact row_strip419_sum
  · exact row_strip420_sum
  · exact row_strip421_sum
  · exact row_strip422_sum
  · exact row_strip423_sum
  · exact row_strip424_sum
  · exact row_strip425_sum
  · exact row_strip426_sum
  · exact row_strip427_sum
  · exact row_strip428_sum
  · exact row_strip429_sum
  · exact row_strip430_sum
  · exact row_strip431_sum
  · exact row_strip432_sum
  · exact row_strip433_sum
  · exact row_strip434_sum
  · exact row_strip435_sum
  · exact row_strip436_sum
  · exact row_strip437_sum
  · exact row_strip438_sum
  · exact row_strip439_sum
  · exact row_strip440_sum
  · exact row_strip441_sum
  · exact row_strip442_sum
  · exact row_strip443_sum
  · exact row_strip444_sum
  · exact row_strip445_sum
  · exact row_strip446_sum
  · exact row_strip447_sum
  · exact row_strip448_sum
  · exact row_strip449_sum
  · exact row_strip450_sum
  · exact row_strip451_sum
  · exact row_strip452_sum
  · exact row_strip453_sum
  · exact row_strip454_sum
  · exact row_strip455_sum
  · exact row_strip456_sum
  · exact row_strip457_sum
  · exact row_strip458_sum
  · exact row_strip459_sum
  · exact row_strip460_sum
  · exact row_strip461_sum
  · exact row_strip462_sum
  · exact row_strip463_sum
  · exact row_strip464_sum
  · exact row_strip465_sum
  · exact row_strip466_sum
  · exact row_strip467_sum
  · exact row_strip468_sum
  · exact row_strip469_sum
  · exact row_strip470_sum
  · exact row_strip471_sum
  · exact row_strip472_sum
  · exact row_strip473_sum
  · exact row_strip474_sum
  · exact row_strip475_sum
  · exact row_strip476_sum
  · exact row_strip477_sum
  · exact row_strip478_sum
  · exact row_strip479_sum
  · exact row_strip480_sum
  · exact row_strip481_sum
  · exact row_strip482_sum
  · exact row_strip483_sum
  · exact row_strip484_sum
  · exact row_strip485_sum
  · exact row_strip486_sum
  · exact row_strip487_sum
  · exact row_strip488_sum
  · exact row_strip489_sum
  · exact row_strip490_sum
  · exact row_strip491_sum
  · exact row_strip492_sum
  · exact row_strip493_sum
  · exact row_strip494_sum
  · exact row_strip495_sum
  · exact row_strip496_sum
  · exact row_strip497_sum
  · exact row_strip498_sum
  · exact row_strip499_sum
  · exact row_strip500_sum
  · exact row_strip501_sum
  · exact row_strip502_sum
  · exact row_strip503_sum
  · exact row_strip504_sum
  · exact row_strip505_sum
  · exact row_strip506_sum
  · exact row_strip507_sum
  · exact row_strip508_sum
  · exact row_strip509_sum
  · exact row_strip510_sum
  · exact row_strip511_sum

/-- Exact original savedQ80 sum; not the distinct natural-endpoint certificate. -/
theorem frozen_saved_total :
    (∑ r : Row, (frozenSavedRow r).savedQ80) = (11290806845175652020270 : ℤ) := by
  rw [Fintype.sum_sigma]
  simp_rw [all_strip_sums]
  decide +kernel

end ImbalancedChen.P2HistoricalSavedFloorStoredTotal
