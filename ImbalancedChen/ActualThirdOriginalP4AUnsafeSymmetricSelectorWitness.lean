import ImbalancedChen.ActualThirdOriginalP4AOrdinaryFiniteSelector
import ImbalancedChen.ActualThirdOriginalSymmetricJensenLeaf

/-! SOURCEONLY / UNCOMPILED / OPEN30.
An exact symbolic family disproving exclusion of the unsafe xz/fall branch.
No numerical replay, endpoint factor query, or desired integral bound is used.
The tuple scales to the original D=48000*2^24 integer grid exactly. -/
namespace ImbalancedChen.OriginalThirdP4AUnsafeSymmetricSelectorWitnessSourceOnly

noncomputable section
open OriginalThirdBoxMomentsSourceOnly
open OriginalThirdSixTentCandidatesSourceOnly
open OriginalThirdLiteralTentSelectorGuardBridgeSourceOnly
open OriginalThirdP4AOrdinaryFiniteSelectorSourceOnly
open OriginalThirdSortedHalfIntegralSourceOnly

def witnessLo (J : ℤ) : Fin 3 → ℤ := ![168*J,168*J,32*J]
def witnessHi (J : ℤ) : Fin 3 → ℤ := ![169*J,169*J,33*J]

theorem witness_sourceCandidates (J T : ℤ) (hJ : 0 < J) (hT : 612*J ≤ T) :
    sourceCandidates (witnessLo J) (witnessHi J) (1024*J) T =
      [.base, .tent .x .rise, .tent .y .rise, .tent .xy .fall,
        .tent .xz .fall, .tent .yz .fall, .tent .xyz .fall] := by
  classical
  have hx : deltaNumerator (1024*J) .x (witnessHi J) ≤ 0 := by
    norm_num [deltaNumerator, rawSum, witnessHi, literalTentX, literalTentY,
      literalTentZ] <;> omega
  have hy : deltaNumerator (1024*J) .y (witnessHi J) ≤ 0 := by
    norm_num [deltaNumerator, rawSum, witnessHi, literalTentX, literalTentY,
      literalTentZ] <;> omega
  have hxy : ¬ deltaNumerator (1024*J) .xy (witnessHi J) ≤ 0 := by
    norm_num [deltaNumerator, rawSum, witnessHi, literalTentX, literalTentY,
      literalTentZ] <;> omega
  have hxyl : 0 ≤ deltaNumerator (1024*J) .xy (witnessLo J) := by
    norm_num [deltaNumerator, rawSum, witnessLo, literalTentX, literalTentY,
      literalTentZ] <;> omega
  have hxz : ¬ deltaNumerator (1024*J) .xz (witnessHi J) ≤ 0 := by
    norm_num [deltaNumerator, rawSum, witnessHi, literalTentX, literalTentY,
      literalTentZ] <;> omega
  have hxzl : 0 ≤ deltaNumerator (1024*J) .xz (witnessLo J) := by
    norm_num [deltaNumerator, rawSum, witnessLo, literalTentX, literalTentY,
      literalTentZ] <;> omega
  have hyz : ¬ deltaNumerator (1024*J) .yz (witnessHi J) ≤ 0 := by
    norm_num [deltaNumerator, rawSum, witnessHi, literalTentX, literalTentY,
      literalTentZ] <;> omega
  have hyzl : 0 ≤ deltaNumerator (1024*J) .yz (witnessLo J) := by
    norm_num [deltaNumerator, rawSum, witnessLo, literalTentX, literalTentY,
      literalTentZ] <;> omega
  have hxyz : ¬ deltaNumerator (1024*J) .xyz (witnessHi J) ≤ 0 := by
    norm_num [deltaNumerator, rawSum, witnessHi, literalTentX, literalTentY,
      literalTentZ] <;> omega
  have hxyzl : 0 ≤ deltaNumerator (1024*J) .xyz (witnessLo J) := by
    norm_num [deltaNumerator, rawSum, witnessLo, literalTentX, literalTentY,
      literalTentZ] <;> omega
  have hraw : sourceRaw (witnessLo J) (witnessHi J) (1024*J) =
      [.base, .tent .x .rise, .tent .y .rise, .tent .xy .fall,
        .tent .xz .fall, .tent .yz .fall, .tent .xyz .fall] := by
    simp [sourceRaw, sourceSums, sourcePair, hx, hy, hxy, hxyl,
      hxz, hxzl, hyz, hyzl, hxyz, hxyzl]
  have hrB : rootTest (witnessLo J) (witnessHi J) (1024*J) T .base := by
    norm_num [rootTest, witnessLo] <;> omega
  have hrX : rootTest (witnessLo J) (witnessHi J) (1024*J) T (.tent .x .rise) := by
    norm_num [rootTest, rawSum, witnessHi, literalTentX, literalTentY,
      literalTentZ] <;> omega
  have hrY : rootTest (witnessLo J) (witnessHi J) (1024*J) T (.tent .y .rise) := by
    norm_num [rootTest, rawSum, witnessHi, literalTentX, literalTentY,
      literalTentZ] <;> omega
  have hrXY : rootTest (witnessLo J) (witnessHi J) (1024*J) T (.tent .xy .fall) := by
    norm_num [rootTest, rawSum, witnessLo, literalTentX, literalTentY,
      literalTentZ] <;> omega
  have hrXZ : rootTest (witnessLo J) (witnessHi J) (1024*J) T (.tent .xz .fall) := by
    norm_num [rootTest, rawSum, witnessLo, literalTentX, literalTentY,
      literalTentZ] <;> omega
  have hrYZ : rootTest (witnessLo J) (witnessHi J) (1024*J) T (.tent .yz .fall) := by
    norm_num [rootTest, rawSum, witnessLo, literalTentX, literalTentY,
      literalTentZ] <;> omega
  have hrXYZ : rootTest (witnessLo J) (witnessHi J) (1024*J) T (.tent .xyz .fall) := by
    norm_num [rootTest, rawSum, witnessLo, literalTentX, literalTentY,
      literalTentZ] <;> omega
  unfold sourceCandidates
  rw [hraw]
  simp [hrB, hrX, hrY, hrXY, hrXZ, hrYZ, hrXYZ]

theorem witness_scores (J : ℤ) :
    sourceScore (witnessLo J) (witnessHi J) (1024*J) .base = (9597:ℚ)/8*(J:ℚ) ∧
    sourceScore (witnessLo J) (witnessHi J) (1024*J) (.tent .x .rise) = (2385:ℚ)/2*(J:ℚ) ∧
    sourceScore (witnessLo J) (witnessHi J) (1024*J) (.tent .y .rise) = (2385:ℚ)/2*(J:ℚ) ∧
    sourceScore (witnessLo J) (witnessHi J) (1024*J) (.tent .xy .fall) = 813*(J:ℚ) ∧
    sourceScore (witnessLo J) (witnessHi J) (1024*J) (.tent .xz .fall) = 1221*(J:ℚ) ∧
    sourceScore (witnessLo J) (witnessHi J) (1024*J) (.tent .yz .fall) = 1221*(J:ℚ) ∧
    sourceScore (witnessLo J) (witnessHi J) (1024*J) (.tent .xyz .fall) = (1431:ℚ)/2*(J:ℚ) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    norm_num [sourceScore, rangeLow, rangeHigh, rawSum, witnessLo, witnessHi,
      literalTentX, literalTentY, literalTentZ] <;> push_cast <;> ring

/-- A closed dominance lemma: B and every distinct non-tied source candidate
lose to xz/fall. No selected-candidate or desired dominance premise is used. -/
theorem witness_strict_dominance (J : ℤ) (hJ : 0 < J) (p : Candidate)
    (hp : p ∈ [.base, .tent .x .rise, .tent .y .rise,
      .tent .xy .fall, .tent .xyz .fall]) :
    sourceScore (witnessLo J) (witnessHi J) (1024*J) p <
      sourceScore (witnessLo J) (witnessHi J) (1024*J) (.tent .xz .fall) := by
  have hJQ : (0:ℚ) < (J:ℚ) := by exact_mod_cast hJ
  obtain ⟨hB,hX,hY,hXY,hXZ,hYZ,hXYZ⟩ := witness_scores J
  simp only [List.mem_cons, List.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl <;>
    simp only [hB, hX, hY, hXY, hXZ, hXYZ] <;> nlinarith

/-- The actual original first-max selector chooses the unsafe xz/fall plane.
The later yz/fall ties its score but loses by source enumeration priority. -/
theorem witness_originalMinorant (J T : ℤ) (hJ : 0 < J) (hT : 612*J ≤ T) :
    originalMinorant (witnessLo J) (witnessHi J) (1024*J) T =
      some (.tent .xz .fall) := by
  have hJQ : (0:ℚ) < (J:ℚ) := by exact_mod_cast hJ
  obtain ⟨hB,hX,hY,hXY,hXZ,hYZ,hXYZ⟩ := witness_scores J
  have hBlt : (9597:ℚ)/8*(J:ℚ) < 1221*(J:ℚ) := by nlinarith
  have hXlt : (2385:ℚ)/2*(J:ℚ) < 1221*(J:ℚ) := by nlinarith
  have hXYlt : (813:ℚ)*(J:ℚ) < 1221*(J:ℚ) := by nlinarith
  have hXYZlt : (1431:ℚ)/2*(J:ℚ) < 1221*(J:ℚ) := by nlinarith
  unfold originalMinorant
  rw [witness_sourceCandidates J T hJ hT]
  simp [firstMax, hB, hX, hY, hXY, hXZ, hYZ, hXYZ,
    not_le_of_gt hBlt, not_le_of_gt hXlt, not_le_of_gt hXYlt, hXYZlt.le]

/-- Specialization to the exact original integer denominator and root value.
The parameter is a symbolic common grid factor, not a numerical replay. -/
theorem witness_original_grid :
    originalMinorant (witnessLo (48000*2^14)) (witnessHi (48000*2^14))
      (48000*2^24) 481573208064 = some (.tent .xz .fall) := by
  have hD : (48000*2^24:ℤ) = 1024*(48000*2^14) := by norm_num
  rw [hD]
  exact witness_originalMinorant _ _ (by norm_num) (by norm_num)

theorem witness_coordinate_bindings (J : ℤ) (hJ : 0 < J) :
    ((witnessLo J 0 : ℤ):ℝ)/((1024*J:ℤ):ℝ) = 21/128 ∧
    ((witnessHi J 0 : ℤ):ℝ)/((1024*J:ℤ):ℝ) = 169/1024 ∧
    ((witnessLo J 2 : ℤ):ℝ)/((1024*J:ℤ):ℝ) = 1/32 ∧
    ((witnessHi J 2 : ℤ):ℝ)/((1024*J:ℤ):ℝ) = 33/1024 := by
  have hJR : (0:ℝ) < (J:ℝ) := by exact_mod_cast hJ
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    norm_num [witnessLo, witnessHi] <;> push_cast <;>
    field_simp [hJR.ne'] <;> ring

/-- The witness lies in the actual full symmetric BELOW-mu geometry. -/
theorem witness_symmetric_full_box :
    SymmetricFullBox (21/128) (169/1024) (1/32) (33/1024) := by
  constructor <;> norm_num [thirdPrefixRho, thirdPrefixTheta, VariableEnvelope.mu]

theorem witness_old_support_and_unsafe_coefficients :
    tentOldLow .xz .fall (![169/1024,169/1024,33/1024] : BoxPoint) = 238/33 ∧
    tentOldHigh .xz .fall (![21/128,21/128,1/32] : BoxPoint) = 61/8 ∧
    (2:ℝ) ≤ 238/33 ∧ (238:ℝ)/33 < 61/8 ∧ (61:ℝ)/8 < 12 ∧
    0 < oldNumerator .xz .fall (![169/1024,169/1024,33/1024] : BoxPoint) ∧
    oldX .xz .fall - oldY .xz .fall = -(3:ℝ)/2 := by
  norm_num [tentOldLow, tentOldHigh, tentOldArgument, affineArgument,
    oldNumerator, oldX, oldY, oldZ, planeConst, planeSlope, sumX, sumY, sumZ]

end
end ImbalancedChen.OriginalThirdP4AUnsafeSymmetricSelectorWitnessSourceOnly
