import ImbalancedChen.P1OriginalThirdGammaValueStability
import ImbalancedChen.P1OriginalFifthActualOwnerCrossingVolume

-- SOURCE ONLY / UNCOMPILED_ZERO_CREDIT / HELD IMPORTS / ready=false.
-- Gamma VALUE monotonicity and a SAME-mesh SAME-owner volume rate.
-- No pair-Boolean constancy, changing-mesh limit, or all-table claim.
namespace ImbalancedChen.P1OriginalFifthGammaRateOwnerVolume

noncomputable section
open MeasureTheory Set
open scoped Classical
open HistoricalThirdCoarse VariableEnvelope
open P1OriginalPrefixRowDecodeSoundness P1OriginalVariableFifthContinuation
open P1OriginalFifthGrid400RefinedFullBoxCover
open HistoricalThirdCoarse.P1OriginalCoarseFifth
open P1OriginalCoarseFifthContinuation P1FifthUnitBoxGainDecomposition
open P1OriginalFifthActualOwnerGateCrossing P1OriginalFifthActualOwnerCrossingVolume

-- A removed pair is replaced by the baseline, which is already an outer
-- max entry. Thus its removal cannot increase the actual full rule.
theorem fullGamma_antitone (b : RationalBox) : Antitone (fun e : ℝ => fullGamma e b) := by
  intro e0 e1 he
  have hbase : qVLo b.lx b.ux ≤ fullGamma e0 b := baseline_le_fullGamma e0 b
  have hxy : qVLo (b.lx+b.ly) (b.ux+b.uy) ≤ fullGamma e0 b := by
    unfold fullGamma
    exact le_max_of_le_right (le_max_left _ _)
  have hxyz : qVLo (b.lx+b.ly+b.lz) (b.ux+b.uy+b.uz) ≤ fullGamma e0 b := by
    unfold fullGamma
    exact le_max_of_le_right (le_max_of_le_right (le_max_left _ _))
  have hr : rescue b ≤ fullGamma e0 b := by
    unfold fullGamma
    exact le_max_of_le_right (le_max_of_le_right
      (le_max_of_le_right (le_max_left _ _)))
  have hxz : (if e1 ≤ xzGap b then qVLo (b.lx+b.lz) (b.ux+b.uz)
      else qVLo b.lx b.ux) ≤ fullGamma e0 b := by
    by_cases h1 : e1 ≤ xzGap b
    · rw [if_pos h1]
      have h0 : e0 ≤ xzGap b := he.trans h1
      unfold fullGamma
      rw [if_pos h0]
      exact le_max_of_le_right (le_max_of_le_right
        (le_max_of_le_right (le_max_of_le_right (le_max_left _ _))))
    · rw [if_neg h1]
      exact hbase
  have hyz : (if e1 ≤ yzGap b then qVLo (b.ly+b.lz) (b.uy+b.uz)
      else qVLo b.lx b.ux) ≤ fullGamma e0 b := by
    by_cases h1 : e1 ≤ yzGap b
    · rw [if_pos h1]
      have h0 : e0 ≤ yzGap b := he.trans h1
      unfold fullGamma
      rw [if_pos h0]
      exact le_max_of_le_right (le_max_of_le_right
        (le_max_of_le_right (le_max_of_le_right (le_max_right _ _))))
    · rw [if_neg h1]
      exact hbase
  unfold fullGamma
  dsimp only
  simp only [max_le_iff]
  exact ⟨hbase,hxy,hxyz,hr,hxz,hyz⟩

-- The outer mu-4e dispatch has the same direction. No key77 or width
-- assumption is needed for this exact one-sided monotonicity statement.
theorem gamma_antitone (b : RationalBox) : Antitone (fun e : ℝ => gamma e b) := by
  intro e0 e1 he
  by_cases h1 : (b.ux:ℝ) ≤ mu-4*e1
  · have h0 : (b.ux:ℝ) ≤ mu-4*e0 := by linarith
    rw [gamma,if_pos h1,gamma,if_pos h0]
    exact fullGamma_antitone b he
  · rw [gamma,if_neg h1]
    exact baseline_le_gamma e0 b

theorem actual_refined_gamma_drop_bounds
    (q : ℕ) (hq : 0 < q) (raw : FifthWireRow)
    (j : Fin 5 → Fin (refinedMesh q+1)) (e chi : ℝ)
    (he : 0 ≤ e) (hemax : e ≤ 3/51200) (hchi : chi ≤ e/10)
    (hstep : logPrimeMeshStep 0 (19/96) (refinedMesh q) ≤ chi)
    (hgrid : raw.grid = 400) (hkey : raw.lo 0 ≤ 77)
    (hcontained : fifthCellContained raw (refinedMesh q) j)
    (hadopted : thirdOwner j ∈ cells e chi (refinedMesh q)) :
    let b := box (refinedMesh q) (thirdOwner j)
    0 ≤ (gamma 0 b:ℝ)-(gamma e b:ℝ) ∧
      (gamma 0 b:ℝ)-(gamma e b:ℝ) ≤ e/20 := by
  let b := box (refinedMesh q) (thirdOwner j)
  have hmono : (gamma e b:ℝ) ≤ (gamma 0 b:ℝ) := by
    exact_mod_cast gamma_antitone b he
  have hvalue := P1OriginalThirdGammaValueStability.actual_refined_grid400_gamma_zero_le_buffer
    q hq raw j e chi he hemax hchi hstep hgrid hkey hcontained hadopted
  change 0 ≤ (gamma 0 b:ℝ)-(gamma e b:ℝ) ∧
    (gamma 0 b:ℝ)-(gamma e b:ℝ) ≤ e/20
  constructor <;> linarith

theorem actual_refined_thirdDifference_rate
    (q : ℕ) (hq : 0 < q) (raw : FifthWireRow)
    (j : Fin 5 → Fin (refinedMesh q+1)) (e : ℚ) (chi : ℝ)
    (he : 0 ≤ e) (hemax : e ≤ 3/51200) (hchi : chi ≤ (e:ℝ)/10)
    (hstep : logPrimeMeshStep 0 (19/96) (refinedMesh q) ≤ chi)
    (hgrid : raw.grid = 400) (hkey : raw.lo 0 ≤ 77)
    (hcontained : fifthCellContained raw (refinedMesh q) j)
    (hadopted : thirdOwner j ∈ cells (e:ℝ) chi (refinedMesh q)) :
    thirdDifference 0 e (refinedMesh q) j ≤ 41*(e:ℝ)/20 := by
  have heR : (0:ℝ) ≤ e := by exact_mod_cast he
  have hemaxR : (e:ℝ) ≤ 3/51200 := by exact_mod_cast hemax
  have hd := actual_refined_gamma_drop_bounds q hq raw j (e:ℝ) chi heR hemaxR
    hchi hstep hgrid hkey hcontained hadopted
  let b := box (refinedMesh q) (thirdOwner j)
  change |levelExponent 0 b - levelExponent (e:ℝ) b| ≤ 41*(e:ℝ)/20
  have hn : 0 ≤ levelExponent 0 b - levelExponent (e:ℝ) b := by
    dsimp only [levelExponent]
    linarith [hd.1]
  rw [abs_of_nonneg hn]
  dsimp only [levelExponent]
  linarith [hd.2]

-- Both genuine selected-cell predicates and both literal firstStop
-- checks are retained. Their existence is not inferred from the rate.
theorem actual_same_owner_symmDiff_volume_rate
    (q : ℕ) (hq : 0 < q) (raw : FifthWireRow)
    (j : Fin 5 → Fin (refinedMesh q+1)) (e : ℚ)
    (chi0 chi omega0 omega : ℝ)
    (J0 J : Finset (Label5 (refinedMesh q)))
    (he : 0 ≤ e) (hemax : e ≤ 3/51200) (hchi : chi ≤ (e:ℝ)/10)
    (hstep : logPrimeMeshStep 0 (19/96) (refinedMesh q) ≤ chi)
    (hgrid : raw.grid = 400) (hkey : raw.lo 0 ≤ 77)
    (hcontained : fifthCellContained raw (refinedMesh q) j)
    (hj0 : j ∈ selectedFifthCells 0 chi0 (refinedMesh q) omega0 J0)
    (hj : j ∈ selectedFifthCells e chi (refinedMesh q) omega J)
    (hs0 : P1OriginalHistoricalFifthOwnCubeAffineGates.firstStopCellCheck
      0 (refinedMesh q) j = true)
    (hs : P1OriginalHistoricalFifthOwnCubeAffineGates.firstStopCellCheck
      (e:ℝ) (refinedMesh q) j = true) :
    volume ((rawOwnerDomain raw 0 chi0 (refinedMesh q) omega0 j \
        rawOwnerDomain raw e chi (refinedMesh q) omega j) ∪
      (rawOwnerDomain raw e chi (refinedMesh q) omega j \
        rawOwnerDomain raw 0 chi0 (refinedMesh q) omega0 j)) ≤
      ENNReal.ofReal (61*(e:ℝ)/(30*(400:ℝ)^4)) := by
  have hadopted := ((mem_selectedFifthCells e chi (refinedMesh q) omega J j).mp hj).2.1
  have hthird := actual_refined_thirdDifference_rate q hq raw j e chi he hemax
    hchi hstep hgrid hkey hcontained hadopted
  have heR : (0:ℝ) ≤ e := by exact_mod_cast he
  have hinit : initialDifference 0 e = 2*(e:ℝ) := by
    rw [initialDifference_eq_twice_buffer]
    simp only [Rat.cast_zero,zero_sub,abs_neg,abs_of_nonneg heR]
  have hcross := fixedOwnerBase_crossing_volume_le raw hgrid 0 e (refinedMesh q) j
  have hrate : (initialDifference 0 e + 2*thirdDifference 0 e (refinedMesh q) j) /
      (3*(400:ℝ)^4) ≤ 61*(e:ℝ)/(30*(400:ℝ)^4) := by
    rw [hinit]
    nlinarith
  exact (measure_mono (selected_owner_difference_subset_gate_crossing
    raw 0 e chi0 chi (refinedMesh q) omega0 omega J0 J j hj0 hj hs0 hs)).trans
      (hcross.trans (ENNReal.ofReal_le_ofReal hrate))

end
end ImbalancedChen.P1OriginalFifthGammaRateOwnerVolume
