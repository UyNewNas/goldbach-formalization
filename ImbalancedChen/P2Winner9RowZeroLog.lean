import ImbalancedChen.P2Winner9GenericLogBranch
import ImbalancedChen.P2Winner9RowArithmeticChecker
import ImbalancedChen.P2Winner9CompleteSeedBlock00

/-! Exact log-selected floor for the first original Winner9 archive row. -/

namespace ImbalancedChen.P2Winner9RowZeroLog

open MeasureTheory
open P2Winner9CompleteSeedTypes (RawRow)
open P2Winner9CurvatureExactMomentFloor (q96)
open P2Winner9GenericLogBranch
open P2Winner9PhysicalAffineTransfer (physicalUpperIntegrand)
open P2Winner9RowArithmeticChecker (archiveVertices fastDet fastDet_eq)
open P2Winner9SelectedRowEdgeGeometry (edgeMatrix)
open P2Winner9SelectedRowIntegerScales (rawGap rawFactor)
open P2Winner9SelectedRowRealJacobian (RationalVertices sourceSupport)

set_option maxRecDepth 50000
set_option maxHeartbeats 40000000

def raw : RawRow := P2Winner9CompleteSeedBlock00.rows[0]!

def verts : RationalVertices := ![
  ![((2281219 : ℚ) / 16000000), ((1500001 : ℚ) / 12000000), ((2156269 : ℚ) / 24000000), ((843749 : ℚ) / 16000000), ((843749 : ℚ) / 16000000), ((843749 : ℚ) / 16000000), ((843749 : ℚ) / 48000000), ((843749 : ℚ) / 48000000)],
  ![((6109297 : ℚ) / 45000000), ((2234381 : ℚ) / 22500000), ((2234381 : ℚ) / 22500000), ((2234381 : ℚ) / 45000000), ((2234381 : ℚ) / 45000000), ((2234381 : ℚ) / 45000000), ((7 : ℚ) / 192), ((7 : ℚ) / 192)],
  ![((57 : ℚ) / 512), ((57 : ℚ) / 512), ((57 : ℚ) / 512), ((1015633 : ℚ) / 16000000), ((2546867 : ℚ) / 48000000), ((2140681 : ℚ) / 48000000), ((328117 : ℚ) / 16000000), ((328117 : ℚ) / 16000000)],
  ![((57 : ℚ) / 512), ((57 : ℚ) / 512), ((57 : ℚ) / 512), ((57 : ℚ) / 1024), ((57 : ℚ) / 1024), ((57 : ℚ) / 1024), ((19 : ℚ) / 1024), ((19 : ℚ) / 1024)],
  ![((5 : ℚ) / 48), ((5 : ℚ) / 48), ((5 : ℚ) / 48), ((5 : ℚ) / 96), ((5 : ℚ) / 96), ((5 : ℚ) / 96), ((7 : ℚ) / 192), ((7 : ℚ) / 192)],
  ![((5 : ℚ) / 48), ((5 : ℚ) / 48), ((5 : ℚ) / 48), ((5 : ℚ) / 96), ((5 : ℚ) / 96), ((5 : ℚ) / 96), ((7 : ℚ) / 192), ((218747 : ℚ) / 10500000)],
  ![((3661457 : ℚ) / 36000000), ((3661457 : ℚ) / 36000000), ((3661457 : ℚ) / 36000000), ((2494801 : ℚ) / 36000000), ((2494801 : ℚ) / 36000000), ((18229 : ℚ) / 562500), ((18229 : ℚ) / 750000), ((18229 : ℚ) / 750000)],
  ![((25484363 : ℚ) / 252000000), ((25484363 : ℚ) / 252000000), ((25484363 : ℚ) / 252000000), ((2640637 : ℚ) / 36000000), ((16296863 : ℚ) / 252000000), ((7 : ℚ) / 192), ((7 : ℚ) / 192), ((218747 : ℚ) / 10500000)],
  ![((25484363 : ℚ) / 252000000), ((25484363 : ℚ) / 252000000), ((25484363 : ℚ) / 252000000), ((2640637 : ℚ) / 36000000), ((25484363 : ℚ) / 504000000), ((25484363 : ℚ) / 504000000), ((7 : ℚ) / 192), ((218747 : ℚ) / 10500000)]
]

private theorem match_vertex_coordinates : ∀ (i : Fin 9) (j : Fin 8),
    archiveVertices raw i j = verts i j := by
  decide +kernel

theorem match_vertices : archiveVertices raw = verts :=
  funext fun i => funext (match_vertex_coordinates i)

def geometry : Geometry where
  vertices := verts
  det_ne := by rw [← fastDet_eq]; decide +kernel
  gap_nonneg := by decide +kernel
  gap_sum_pos := by decide +kernel
  factor_pos := by decide +kernel

def storedGaps : Fin 10 → ℕ := ![1478429165365317600517, 1653604571461928418391, 884230650012315527426, 271756649424121147329, 192747521203985537787, 1385542142337246235572, 808653339177585537865, 1610200061604707219745, 4709548128863066453763, 4612618502086657143400]

def storedJensen : ℚ := ((1713377773745812874977616927470884503885507680960459190101847773806422088988123610503720366462243014308458366318080000000000000000000000000000 : ℚ) / 95582375286741983725833648537412974438153885152316048465638963144847708785863496187389166775263396039008238356866363473194304666546678591251128452481)

theorem match_approx : raw.jensen = storedJensen ∧
    (∀ j : Fin 10, raw.logGapFloors[j.val]! = storedGaps j) ∧ raw.logSelected = raw.mixedSelected := by
  decide +kernel

theorem jensen_reconstruct : storedJensen = jensenQ geometry := by
  rw [jensenQ, ← fastDet_eq]
  decide +kernel

theorem gaps_directed : ∀ j, savedGapQ storedGaps j ≤ logGapQ geometry j := by
  intro j
  fin_cases j <;> decide +kernel

theorem price_directed : (raw.logSelected : ℚ) / q96 ≤ logPriceQ storedJensen storedGaps := by
  decide +kernel

/-- The first archive row's log-selected price bounds its actual physical integral. -/
theorem row_zero_selected_floor :
    (raw.mixedSelected : ℝ) / (q96 : ℝ) ≤
      ∫ z in sourceSupport (archiveVertices raw), physicalUpperIntegrand z := by
  rw [← match_approx.2.2, match_vertices]
  exact directed_log_floor geometry storedJensen storedGaps raw.logSelected jensen_reconstruct
    gaps_directed price_directed

theorem log_wins : raw.mixedRaw < raw.logSelected := by decide +kernel


end ImbalancedChen.P2Winner9RowZeroLog
