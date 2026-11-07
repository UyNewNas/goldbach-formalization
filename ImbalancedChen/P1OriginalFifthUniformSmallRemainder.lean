import ImbalancedChen.P1FifthMiddleNormalizedPointwise
import ImbalancedChen.P1OriginalFifthMiddleShellRemainderSplit
import Mathlib.Topology.Order.LiminfLimsup

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

Uniform small-cutoff passage for the SAME original coarse fifth dictionary.
The actual arbitrary-residual lower-source supplier, original third-parent
gaps, moving quadratic prime-shell moment, exact signed split and proved
ultratiny moving-tail limit are composed here. No pointwise target bound,
shell mean or desired remainder conclusion is assumed. This module does
not identify this coarse dictionary with the corrected variable-old source.
-/

namespace ImbalancedChen.P1OriginalFifthUniformSmallRemainder

noncomputable section
open Filter Topology
open scoped Classical BigOperators
open P1OriginalCoarseFifthContinuation
open HistoricalThirdCoarse.P1OriginalCoarseFifth
open P1OriginalFifthWeightedSourceReduction
open P1OriginalFifthMovingScaleLimit
open P1OriginalFifthMiddleShellBinMoment
open P1OriginalFifthMiddleShellFiniteBudget
open P1OriginalFifthMiddleShellMovingLimit
open P1OriginalFifthMiddleShellRemainderSplit
open P1FifthMiddleNormalizedPointwise

private theorem evenTargets_neBot : NeBot evenTargets := by
  have hd : Tendsto (fun n : ℕ => 2 * (n + 1)) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [eventually_ge_atTop b] with n hn
    omega
  have he : Tendsto (fun n : ℕ => 2 * (n + 1)) atTop
      (Filter.principal {N : ℕ | 0 < N ∧ Even N}) := by
    apply tendsto_principal.2
    exact Eventually.of_forall (fun n => ⟨by omega, ⟨n + 1, by omega⟩⟩)
  exact (tendsto_inf.2 ⟨hd, he⟩).neBot

/-- The generic actual same-cutoff lower pair specializes to the literal
coarse cellDifference. Both own-cube gates are proved from the original
third cube before removing them. The constants precede every cutoff. -/
theorem exists_eventually_cellDifference_quadratic :
    ∃ C : ℝ, 0 < C ∧ ∀ (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ),
      0 < omega → ∀ (J4 : Finset (Label4 m)) (cap4 : Label4 m → ℚ)
        (J5 : Finset (Label5 m)) (cap5 : Label5 m → ℚ),
      P1OriginalCoarseContinuation.h34Check e chi m omega J4 cap4 = true →
      h45Check e chi m omega J4 cap4 J5 cap5 = true →
      ∀ a : ℝ, a ≤ omega / 6 →
      ∀ᶠ N : ℕ in evenTargets, ∀ cap : ℕ,
      (N : ℝ) ^ (19 / 96 : ℝ) ≤ (cap : ℝ) →
      ∀ j ∈ selectedFifthCells e chi m omega J5,
      ∀ p ∈ shellCell e chi m omega (movingCutoff omega N) a N cap j,
      |cellDifference e chi m omega J4 cap4 cap5 N cap j p| ≤
        (C / omega ^ 3) * (actualPrimeTupleLog N p 4) ^ 2 := by
  obtain ⟨C, hC, hsource⟩ := exists_eventually_actualMinus_middle_quadratic_bound
  refine ⟨C, hC, ?_⟩
  intro e chi m omega homega J4 cap4 J5 cap5 h34 h45 a ha
  filter_upwards [(hsource omega homega).filter_mono inf_le_left,
    (eventually_ge_atTop (2 : ℕ)).filter_mono inf_le_left,
    (show ∀ᶠ N : ℕ in evenTargets, 0 < N ∧ Even N from
      (Filter.eventually_mem_principal _).filter_mono inf_le_right)]
    with N hs hN he cap hcap j hj p hp
  obtain ⟨hp, hmiddle, hsmall, ht⟩ := Finset.mem_filter.mp hp
  have hN' : 1 < N := by omega
  have hc : p ∈ candidates (e : ℝ) chi m omega N cap := by
    simpa only [sourceCarrier, candidates] using hp
  have hd := (mem_candidates_iff_log_on_cell (e : ℝ) chi m omega N cap hN' hcap p j ht).mp hc
  have hpos : ∀ i, 0 < p i := fun i => (hd.1 i).1.pos
  have hg := (mem_jointRegion (e : ℝ) chi m omega j _).mp hd.2
  have hactive := P1OriginalHistoricalFifthOwnCubeAffineGates.selected_cell_rough
    e chi m omega J5 j hj ht
  have hcurrent := P1OriginalHistoricalFifthOwnCubeAffineGates.selected_currentExponent
    e chi m omega J5 j hj ht
  have hcube : actualPrimeTupleLog N p 0 + actualPrimeTupleLog N p 1 +
      3 * actualPrimeTupleLog N p 2 < HistoricalThirdCoarse.levelExponent (e : ℝ)
        (HistoricalThirdCoarse.box m (thirdOwner j)) := by
    simpa only [hcurrent] using hg.2.2.2.2
  have h34j := old5_ge_original_third_of_h34Check e chi m omega J4 cap4 h34 j
  have h45j : (old5 e chi m omega J4 cap4 j : ℝ) ≤ cap5 j := by
    exact_mod_cast h45Check_sound e chi m omega J4 cap4 J5 cap5 h45 j hj
  have hgo := (HistoricalThirdCoarse.P1OriginalSmallCoordinate.fifth_numerator_gap
    omega _ (old5 e chi m omega J4 cap4 j : ℝ) (actualPrimeTupleLog N p)
    hactive hcube (hg.2.1 (by decide : (2 : Fin 5) < 3)) h34j).2
  have hgn := (HistoricalThirdCoarse.P1OriginalSmallCoordinate.fifth_numerator_gap
    omega _ (cap5 j : ℝ) (actualPrimeTupleLog N p)
    hactive hcube (hg.2.1 (by decide : (2 : Fin 5) < 3)) (h34j.trans h45j)).2
  have hgapOld : omega / 2 < (old5 e chi m omega J4 cap4 j : ℝ) -
      ∑ i, actualPrimeTupleLog N p i := by linarith
  have hgapNew : omega / 2 < (cap5 j : ℝ) -
      ∑ i, actualPrimeTupleLog N p i := by linarith
  have hRold := HistoricalThirdCoarse.P1OriginalSmallCoordinate.actual_quotient_gt_rpow_of_gap
    hN' p hpos (old5 e chi m omega J4 cap4 j : ℝ) (omega / 2) hgapOld
  have hRnew := HistoricalThirdCoarse.P1OriginalSmallCoordinate.actual_quotient_gt_rpow_of_gap
    hN' p hpos (cap5 j : ℝ) (omega / 2) hgapNew
  have hgateOld : (∏ i, p i : ℕ) * (p 4 : ℝ) ^ 2 <
      (N : ℝ) ^ (old5 e chi m omega J4 cap4 j : ℝ) := by
    apply (actualPrimeTupleOwnCube_iff hN' p hpos _).mpr
    unfold primeTupleOwnCubeForm
    change (∑ i, actualPrimeTupleLog N p i) + 2 * actualPrimeTupleLog N p 4 < _
    linarith
  have hgateNew : (∏ i, p i : ℕ) * (p 4 : ℝ) ^ 2 < (N : ℝ) ^ (cap5 j : ℝ) := by
    apply (actualPrimeTupleOwnCube_iff hN' p hpos _).mpr
    unfold primeTupleOwnCubeForm
    change (∑ i, actualPrimeTupleLog N p i) + 2 * actualPrimeTupleLog N p 4 < _
    linarith
  have hb := hs cap he.2 (p 4 : ℝ)
    ((N : ℝ) ^ (old5 e chi m omega J4 cap4 j : ℝ) / (∏ i, p i : ℕ))
    ((N : ℝ) ^ (cap5 j : ℝ) / (∏ i, p i : ℕ)) a
    (by exact_mod_cast hpos 4) ((hd.1 4).2.2.2.le.trans hcap) ha
    hmiddle hsmall hRold.le hRnew.le
  have heq : cellDifference e chi m omega J4 cap4 cap5 N cap j p =
      (actualSmallRosserMinusDensity N cap (p 4 : ℝ)
          ((N : ℝ) ^ (cap5 j : ℝ) / (∏ i, p i : ℕ)) -
        actualSmallRosserMinusDensity N cap (p 4 : ℝ)
          ((N : ℝ) ^ (old5 e chi m omega J4 cap4 j : ℝ) / (∏ i, p i : ℕ))) *
          Real.log (N : ℝ) / singularSeries N := by
    simp only [cellDifference, actualPrimeTupleOwnCubeMinus, if_pos hgateNew, if_pos hgateOld]
    ring
  rw [heq]
  simpa only [logCoordinate, actualPrimeTupleLog] using hb

/-- The absolute original coarse remainder is eventually O(a), with one
constant chosen before a and the arbitrary covering enumeration cap. -/
theorem exists_eventually_smallRemainder_abs_le_linear
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (homega : 0 < omega) (homegaRho : omega < (19 / 96 : ℝ))
    (J4 : Finset (Label4 m)) (cap4 : Label4 m → ℚ)
    (J5 : Finset (Label5 m)) (cap5 : Label5 m → ℚ)
    (h34 : P1OriginalCoarseContinuation.h34Check e chi m omega J4 cap4 = true)
    (h45 : h45Check e chi m omega J4 cap4 J5 cap5 = true) :
    ∃ D : ℝ, 0 < D ∧ ∀ a : ℝ, 0 < a → a ≤ min (19 / 96 : ℝ) (omega / 6) →
      ∀ cap : ℕ → ℕ,
      (∀ᶠ N : ℕ in evenTargets, (N : ℝ) ^ (19 / 96 : ℝ) ≤ (cap N : ℝ)) →
      ∀ᶠ N : ℕ in evenTargets,
        |P1OriginalFifthLimit.smallRemainder e chi m omega a J4 cap4 J5 cap5 N (cap N)| ≤ D * a := by
  obtain ⟨C, hC, hpoint⟩ := exists_eventually_cellDifference_quadratic
  obtain ⟨M, hM, hmoment⟩ := exists_original_moving_middle_shell_quadratic_Oa
    omega homega homegaRho
  let q : ℝ := C / omega ^ 3
  let n : ℝ := ((selectedFifthCells e chi m omega J5).card : ℝ)
  let D : ℝ := 1 + q * n * M
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hn : 0 ≤ n := by dsimp [n]; positivity
  refine ⟨D, by dsimp [D]; positivity, ?_⟩
  intro a ha hamax cap hcap
  have haRho := hamax.trans (min_le_left _ _)
  have haomega := hamax.trans (min_le_right _ _)
  have hdelta := original_smallRemainder_movingCutoff_tendsto_zero_of_checks
    e chi m omega homega J4 cap4 J5 cap5 h34 h45 cap hcap
  have hdeltaAbs : ∀ᶠ N : ℕ in evenTargets,
      |P1OriginalFifthLimit.smallRemainder e chi m omega (movingCutoff omega N)
        J4 cap4 J5 cap5 N (cap N)| < a := by
    have hh := hdelta.abs
    simpa only [abs_zero] using hh.eventually (gt_mem_nhds ha)
  filter_upwards [hdeltaAbs,
    ((movingCutoff_tendsto_zero omega).eventually (gt_mem_nhds ha)).filter_mono inf_le_left,
    hpoint e chi m omega homega J4 cap4 J5 cap5 h34 h45 a haomega,
    hmoment e chi m a ha haRho J5, hcap,
    (eventually_ge_atTop (2 : ℕ)).filter_mono inf_le_left]
    with N hsmall hda hp hm hc hN
  have hN' : 1 < N := by omega
  have hs := normalized_signedShell_le_sum_quadraticMoments
    e chi m omega (movingCutoff omega N) a ha J4 cap4 J5 cap5 N (cap N) hN' hc
    1 q (by intro j hj p hmem; simpa only [mul_one, q] using hp (cap N) hc j hj p hmem)
  have hsum : (∑ j ∈ selectedFifthCells e chi m omega J5,
      shellMoment e chi m omega (movingCutoff omega N) a N (cap N) j) ≤ n * (M * a) := by
    calc
      _ ≤ ∑ _j ∈ selectedFifthCells e chi m omega J5, M * a :=
        Finset.sum_le_sum (fun j hj => hm (cap N) hc j hj)
      _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul, n]
  have hshell : |signedShell e chi m omega (movingCutoff omega N) a
      J4 cap4 J5 cap5 N (cap N)| ≤ q * (n * (M * a)) := by
    simpa only [mul_one] using hs.trans (mul_le_mul_of_nonneg_left hsum hq)
  calc
    _ = |P1OriginalFifthLimit.smallRemainder e chi m omega (movingCutoff omega N)
        J4 cap4 J5 cap5 N (cap N) + signedShell e chi m omega (movingCutoff omega N) a
          J4 cap4 J5 cap5 N (cap N)| := congrArg abs
      (smallRemainder_split e chi m omega (movingCutoff omega N) a hda.le
        J4 cap4 J5 cap5 N (cap N) hN' hc)
    _ ≤ |P1OriginalFifthLimit.smallRemainder e chi m omega (movingCutoff omega N)
        J4 cap4 J5 cap5 N (cap N)| + |signedShell e chi m omega (movingCutoff omega N) a
          J4 cap4 J5 cap5 N (cap N)| := abs_add _ _
    _ ≤ a + q * (n * (M * a)) := add_le_add hsmall.le hshell
    _ = D * a := by dsimp [D]; ring

/-- The constant in the even-target limsup is uniform in a and in every
covering physical cap function. This is an actual arithmetic tail bound. -/
theorem exists_smallRemainder_limsup_le_linear
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (homega : 0 < omega) (homegaRho : omega < (19 / 96 : ℝ))
    (J4 : Finset (Label4 m)) (cap4 : Label4 m → ℚ)
    (J5 : Finset (Label5 m)) (cap5 : Label5 m → ℚ)
    (h34 : P1OriginalCoarseContinuation.h34Check e chi m omega J4 cap4 = true)
    (h45 : h45Check e chi m omega J4 cap4 J5 cap5 = true) :
    ∃ D : ℝ, 0 < D ∧ ∀ a : ℝ, 0 < a → a ≤ min (19 / 96 : ℝ) (omega / 6) →
      ∀ cap : ℕ → ℕ,
      (∀ᶠ N : ℕ in evenTargets, (N : ℝ) ^ (19 / 96 : ℝ) ≤ (cap N : ℝ)) →
      0 ≤ limsup (fun N : ℕ =>
        |P1OriginalFifthLimit.smallRemainder e chi m omega a J4 cap4 J5 cap5 N (cap N)|) evenTargets ∧
      limsup (fun N : ℕ =>
        |P1OriginalFifthLimit.smallRemainder e chi m omega a J4 cap4 J5 cap5 N (cap N)|) evenTargets ≤ D * a := by
  obtain ⟨D, hD, hbound⟩ := exists_eventually_smallRemainder_abs_le_linear
    e chi m omega homega homegaRho J4 cap4 J5 cap5 h34 h45
  refine ⟨D, hD, ?_⟩
  intro a ha hamax cap hcap
  letI : NeBot evenTargets := evenTargets_neBot
  have hb := hbound a ha hamax cap hcap
  have hnonneg : ∀ N : ℕ,
      0 ≤ |P1OriginalFifthLimit.smallRemainder e chi m omega a J4 cap4 J5 cap5 N (cap N)| :=
    fun N => abs_nonneg _
  exact ⟨le_limsup_of_frequently_le (Eventually.of_forall hnonneg).frequently
      (isBoundedUnder_of_eventually_le hb),
    limsup_le_of_le (isCoboundedUnder_le_of_le evenTargets hnonneg) hb⟩

/-- Requested order of limits: first limsup along even N, then a decreases
to zero. Only the literal finite h34/h45 policy checkers are inputs. -/
theorem smallRemainder_limsup_cutoff_zero
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (homega : 0 < omega) (homegaRho : omega < (19 / 96 : ℝ))
    (J4 : Finset (Label4 m)) (cap4 : Label4 m → ℚ)
    (J5 : Finset (Label5 m)) (cap5 : Label5 m → ℚ)
    (h34 : P1OriginalCoarseContinuation.h34Check e chi m omega J4 cap4 = true)
    (h45 : h45Check e chi m omega J4 cap4 J5 cap5 = true) :
    ∀ epsilon : ℝ, 0 < epsilon → ∃ delta : ℝ, 0 < delta ∧
      ∀ a : ℝ, 0 < a → a < delta → ∀ cap : ℕ → ℕ,
      (∀ᶠ N : ℕ in evenTargets, (N : ℝ) ^ (19 / 96 : ℝ) ≤ (cap N : ℝ)) →
      0 ≤ limsup (fun N : ℕ =>
        |P1OriginalFifthLimit.smallRemainder e chi m omega a J4 cap4 J5 cap5 N (cap N)|) evenTargets ∧
      limsup (fun N : ℕ =>
        |P1OriginalFifthLimit.smallRemainder e chi m omega a J4 cap4 J5 cap5 N (cap N)|) evenTargets < epsilon := by
  obtain ⟨D, hD, hbound⟩ := exists_smallRemainder_limsup_le_linear
    e chi m omega homega homegaRho J4 cap4 J5 cap5 h34 h45
  intro epsilon hepsilon
  refine ⟨min (19 / 96 : ℝ) (min (omega / 6) (epsilon / D)),
    lt_min (by norm_num) (lt_min (by positivity) (by positivity)), ?_⟩
  intro a ha hadelta cap hcap
  have haRho : a ≤ (19 / 96 : ℝ) :=
    (hadelta.trans_le (min_le_left _ _)).le
  have hinner : a < min (omega / 6) (epsilon / D) :=
    hadelta.trans_le (min_le_right _ _)
  have haomega : a ≤ omega / 6 := (hinner.trans_le (min_le_left _ _)).le
  have hsmall : D * a < epsilon := by
    have hh := (lt_div_iff₀ hD).mp (hinner.trans_le (min_le_right _ _))
    nlinarith
  have hb := hbound a ha (le_min haRho haomega) cap hcap
  exact ⟨hb.1, hb.2.trans_lt hsmall⟩

/-- Filter form of the actual coarse original fifth iterated tail limit. -/
theorem tendsto_smallRemainder_limsup_cutoff_zero
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (homega : 0 < omega) (homegaRho : omega < (19 / 96 : ℝ))
    (J4 : Finset (Label4 m)) (cap4 : Label4 m → ℚ)
    (J5 : Finset (Label5 m)) (cap5 : Label5 m → ℚ)
    (h34 : P1OriginalCoarseContinuation.h34Check e chi m omega J4 cap4 = true)
    (h45 : h45Check e chi m omega J4 cap4 J5 cap5 = true)
    (cap : ℕ → ℕ)
    (hcap : ∀ᶠ N : ℕ in evenTargets, (N : ℝ) ^ (19 / 96 : ℝ) ≤ (cap N : ℝ)) :
    Tendsto (fun a : ℝ => limsup (fun N : ℕ =>
      |P1OriginalFifthLimit.smallRemainder e chi m omega a J4 cap4 J5 cap5 N (cap N)|) evenTargets)
      (𝓝[Set.Ioi 0] (0 : ℝ)) (𝓝 0) := by
  apply Metric.tendsto_nhdsWithin_nhds.2
  intro epsilon hepsilon
  obtain ⟨delta, hdelta, hbound⟩ := smallRemainder_limsup_cutoff_zero
    e chi m omega homega homegaRho J4 cap4 J5 cap5 h34 h45 epsilon hepsilon
  refine ⟨delta, hdelta, ?_⟩
  intro a ha hadist
  have ha0 : 0 < a := ha
  have haDelta : a < delta := by
    simpa only [Real.dist_eq, sub_zero, abs_of_pos ha0] using hadist
  obtain ⟨hlo, hhi⟩ := hbound a ha0 haDelta cap hcap
  simpa only [Real.dist_eq, sub_zero, abs_of_nonneg hlo] using hhi

end

end ImbalancedChen.P1OriginalFifthUniformSmallRemainder
