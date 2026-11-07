import ImbalancedChen.P1CorrectedFifthMiddlePointwise
import ImbalancedChen.P1CorrectedFifthMovingUltratiny
import Mathlib.Topology.Order.LiminfLimsup

/-!
SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

Uniform fixed-a tail closure for the TRUE corrected original-T3 remainder.
The actual producer OLD4 and stored NEW remain in correctedTupleDifference.
The exact corrected signed shell split, genuine moving prime-shell moment,
normalized actual corrected quadratic bound, and true corrected ultratiny
zero-limit are composed. No coarse remainder is substituted at any stage.

The constant precedes both the fixed cutoff and the covering cap function.
For omega>=rho the selected owner support is proved empty pointwise. Thus
the result requires only positive omega, genuine ownership and the finite
stored h45 check. No target mean, desired remainder or convergence premise.
-/

namespace ImbalancedChen.P1CorrectedFifthUniformSmallRemainder

noncomputable section
open Filter Topology Set
open scoped Classical BigOperators
open P2OriginalFourthCapProducerInterface
open P1CorrectedFifthCausalTupleDictionary P1CorrectedFifthStoredH45Check
open P1CorrectedFifthSmallLastGeometry P1CorrectedFifthMiddlePointwise
open P1CorrectedFifthMovingUltratiny P1CorrectedFifthMiddleShellSplit
open P1OriginalFifthMovingScaleLimit P1OriginalFifthMiddleShellMovingLimit
open P1OriginalFifthMiddleShellFiniteBudget P1OriginalFifthMiddleShellBinMoment

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

/-- This degenerate rough regime has no selected owner points at all;
the conclusion is proved from the actual inclusive activation and strict
rho endpoint, independently of arithmetic limits or row levels. -/
theorem corrected_smallRemainder_eq_zero_of_rho_le_omega
    (D : HistoricalPrefixCapData) (J : Finset (FifthLabel D.m))
    (e : ℚ) (chi omega a : ℝ) (hlarge : (19 / 96 : ℝ) ≤ omega)
    (rows : Finset ProducerRow) (licensed : ProducerRow → Prop)
    (howned : P1VariableFifthSelectedStoredBinding.OriginalOwnedRows D J e chi omega)
    (N cap : ℕ) :
    P1CorrectedFifthGlobalSourceAssembly.smallRemainder D J e chi omega rows licensed a N cap = 0 := by
  unfold P1CorrectedFifthGlobalSourceAssembly.smallRemainder
    P1CorrectedFifthGlobalSourceAssembly.smallCellRemainder
  apply Finset.sum_eq_zero
  intro j hj
  apply Finset.sum_eq_zero
  intro p _hp
  by_cases ht : actualPrimeTupleLog N p ∈ logPrimeMeshCell 0 (19 / 96) D.m j
  · have hselected : j ∈ P1OriginalCoarseFifthContinuation.selectedFifthCells
        e chi D.m omega (D.cells5 ∩ J) := by
      rw [← corrected_selected_owners_eq D J e chi omega howned]
      exact hj
    have hactive := P1OriginalHistoricalFifthOwnCubeAffineGates.selected_cell_rough
      e chi D.m omega (D.cells5 ∩ J) j hselected ht
    have hu := (mem_logPrimeBox.mp
      (logPrimeMeshCell_subset_box (by norm_num : (0 : ℝ) ≤ 19 / 96) D.m j ht) 2).2
    exact (False.elim (by linarith))
  · simp only [ht, and_false, if_false, mul_zero]

/-- One positive constant is selected before a and the cap function.
The bound concerns the actual normalized corrected remainder throughout. -/
theorem exists_eventually_corrected_smallRemainder_abs_le_linear
    (D : HistoricalPrefixCapData) (J : Finset (FifthLabel D.m))
    (e : ℚ) (chi omega : ℝ) (homega : 0 < omega)
    (rows : Finset ProducerRow) (licensed : ProducerRow → Prop)
    (howned : P1VariableFifthSelectedStoredBinding.OriginalOwnedRows D J e chi omega)
    (hcheck : storedH45Check D J e rows = true) :
    ∃ L : ℝ, 0 < L ∧ ∀ a : ℝ, 0 < a → a ≤ min (19 / 96 : ℝ) (omega / 6) →
      ∀ cap : ℕ → ℕ,
      (∀ᶠ N : ℕ in evenTargets, (N : ℝ) ^ (19 / 96 : ℝ) ≤ (cap N : ℝ)) →
      ∀ᶠ N : ℕ in evenTargets,
        |P1CorrectedFifthGlobalSourceAssembly.smallRemainder
          D J e chi omega rows licensed a N (cap N)| ≤ L * a := by
  by_cases homegaRho : omega < (19 / 96 : ℝ)
  · obtain ⟨C, hC, hpoint⟩ := exists_eventually_correctedTupleDifference_middle_quadratic_bound
    obtain ⟨M, hM, hmoment⟩ := exists_original_moving_middle_shell_quadratic_Oa
      omega homega homegaRho
    let q : ℝ := C / omega ^ 3
    let n : ℝ := ((D.cells5 ∩ J).card : ℝ)
    let L : ℝ := 1 + q * n * M
    have hq : 0 ≤ q := by dsimp [q]; positivity
    have hn : 0 ≤ n := by dsimp [n]; positivity
    refine ⟨L, by dsimp [L]; positivity, ?_⟩
    intro a ha hamax cap hcap
    have haRho := hamax.trans (min_le_left _ _)
    have haomega := hamax.trans (min_le_right _ _)
    have hdelta := corrected_smallRemainder_movingCutoff_tendsto_zero
      D J e chi omega homega rows licensed howned hcheck cap hcap
    have hdeltaAbs : ∀ᶠ N : ℕ in evenTargets,
        |P1CorrectedFifthGlobalSourceAssembly.smallRemainder D J e chi omega rows licensed
          (movingCutoff omega N) N (cap N)| < a := by
      simpa only [abs_zero] using hdelta.abs.eventually (gt_mem_nhds ha)
    filter_upwards [hdeltaAbs,
      ((movingCutoff_tendsto_zero omega).eventually (gt_mem_nhds ha)).filter_mono inf_le_left,
      (hpoint omega homega).filter_mono inf_le_left,
      hmoment e chi D.m a ha haRho (D.cells5 ∩ J), hcap,
      (eventually_ge_atTop (2 : ℕ)).filter_mono inf_le_left,
      (show ∀ᶠ N : ℕ in evenTargets, 0 < N ∧ Even N from
        (Filter.eventually_mem_principal _).filter_mono inf_le_right)]
      with N hsmall hda hp hm hc hN he
    have hN' : 1 < N := by omega
    have hshell := correctedShell_abs_le_sum_quadraticMoments D J e chi omega rows licensed
      (movingCutoff omega N) a ha N (cap N) hN' hc howned q (by
        intro j hj p hmem
        obtain ⟨hpc, hmiddle, hlast, ht⟩ := Finset.mem_filter.mp hmem
        exact hp D J e chi a rows licensed howned hcheck (cap N) he.2 hc haomega
          p hpc j hj ht hmiddle hlast)
    have hsum : (∑ j ∈ D.cells5 ∩ J,
        shellMoment e chi D.m omega (movingCutoff omega N) a N (cap N) j) ≤ n * (M * a) := by
      calc
        _ ≤ ∑ _j ∈ D.cells5 ∩ J, M * a := by
          apply Finset.sum_le_sum
          intro j hj
          apply hm (cap N) hc j
          rw [← corrected_selected_owners_eq D J e chi omega howned]
          exact hj
        _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul, n]
    have hshell' : |correctedShell D J e chi omega rows licensed
        (movingCutoff omega N) a N (cap N)| ≤ q * (n * (M * a)) :=
      hshell.trans (mul_le_mul_of_nonneg_left hsum hq)
    calc
      _ = |P1CorrectedFifthGlobalSourceAssembly.smallRemainder D J e chi omega rows licensed
          (movingCutoff omega N) N (cap N) +
          correctedShell D J e chi omega rows licensed (movingCutoff omega N) a N (cap N)| :=
        congrArg abs (corrected_smallRemainder_split D J e chi omega rows licensed
          (movingCutoff omega N) a hda.le N (cap N) hN' hc)
      _ ≤ |P1CorrectedFifthGlobalSourceAssembly.smallRemainder D J e chi omega rows licensed
          (movingCutoff omega N) N (cap N)| +
          |correctedShell D J e chi omega rows licensed (movingCutoff omega N) a N (cap N)| :=
        abs_add _ _
      _ ≤ a + q * (n * (M * a)) := add_le_add hsmall.le hshell'
      _ = L * a := by dsimp [L]; ring
  · refine ⟨1, by norm_num, ?_⟩
    intro a ha _hamax cap _hcap
    exact Eventually.of_forall (fun N => by
      rw [corrected_smallRemainder_eq_zero_of_rho_le_omega D J e chi omega a
        (le_of_not_gt homegaRho) rows licensed howned N (cap N), abs_zero, one_mul]
      exact ha.le)

theorem exists_corrected_smallRemainder_limsup_le_linear
    (D : HistoricalPrefixCapData) (J : Finset (FifthLabel D.m))
    (e : ℚ) (chi omega : ℝ) (homega : 0 < omega)
    (rows : Finset ProducerRow) (licensed : ProducerRow → Prop)
    (howned : P1VariableFifthSelectedStoredBinding.OriginalOwnedRows D J e chi omega)
    (hcheck : storedH45Check D J e rows = true) :
    ∃ L : ℝ, 0 < L ∧ ∀ a : ℝ, 0 < a → a ≤ min (19 / 96 : ℝ) (omega / 6) →
      ∀ cap : ℕ → ℕ,
      (∀ᶠ N : ℕ in evenTargets, (N : ℝ) ^ (19 / 96 : ℝ) ≤ (cap N : ℝ)) →
      0 ≤ limsup (fun N : ℕ => |P1CorrectedFifthGlobalSourceAssembly.smallRemainder
        D J e chi omega rows licensed a N (cap N)|) evenTargets ∧
      limsup (fun N : ℕ => |P1CorrectedFifthGlobalSourceAssembly.smallRemainder
        D J e chi omega rows licensed a N (cap N)|) evenTargets ≤ L * a := by
  obtain ⟨L, hL, hbound⟩ := exists_eventually_corrected_smallRemainder_abs_le_linear
    D J e chi omega homega rows licensed howned hcheck
  refine ⟨L, hL, ?_⟩
  intro a ha hamax cap hcap
  letI : NeBot evenTargets := evenTargets_neBot
  have hb := hbound a ha hamax cap hcap
  have hn : ∀ N : ℕ, 0 ≤ |P1CorrectedFifthGlobalSourceAssembly.smallRemainder
      D J e chi omega rows licensed a N (cap N)| := fun _ => abs_nonneg _
  exact ⟨le_limsup_of_frequently_le (Eventually.of_forall hn).frequently
      (isBoundedUnder_of_eventually_le hb),
    limsup_le_of_le (isCoboundedUnder_le_of_le evenTargets hn) hb⟩

/-- The requested order of limits, uniform in the covering cap function. -/
theorem corrected_smallRemainder_limsup_cutoff_zero
    (D : HistoricalPrefixCapData) (J : Finset (FifthLabel D.m))
    (e : ℚ) (chi omega : ℝ) (homega : 0 < omega)
    (rows : Finset ProducerRow) (licensed : ProducerRow → Prop)
    (howned : P1VariableFifthSelectedStoredBinding.OriginalOwnedRows D J e chi omega)
    (hcheck : storedH45Check D J e rows = true) :
    ∀ epsilon : ℝ, 0 < epsilon → ∃ delta : ℝ, 0 < delta ∧
      ∀ a : ℝ, 0 < a → a < delta → ∀ cap : ℕ → ℕ,
      (∀ᶠ N : ℕ in evenTargets, (N : ℝ) ^ (19 / 96 : ℝ) ≤ (cap N : ℝ)) →
      0 ≤ limsup (fun N : ℕ => |P1CorrectedFifthGlobalSourceAssembly.smallRemainder
        D J e chi omega rows licensed a N (cap N)|) evenTargets ∧
      limsup (fun N : ℕ => |P1CorrectedFifthGlobalSourceAssembly.smallRemainder
        D J e chi omega rows licensed a N (cap N)|) evenTargets < epsilon := by
  obtain ⟨L, hL, hbound⟩ := exists_corrected_smallRemainder_limsup_le_linear
    D J e chi omega homega rows licensed howned hcheck
  intro epsilon hepsilon
  refine ⟨min (19 / 96 : ℝ) (min (omega / 6) (epsilon / L)),
    lt_min (by norm_num) (lt_min (by positivity) (by positivity)), ?_⟩
  intro a ha hadelta cap hcap
  have haRho : a ≤ (19 / 96 : ℝ) := (hadelta.trans_le (min_le_left _ _)).le
  have hinner : a < min (omega / 6) (epsilon / L) := hadelta.trans_le (min_le_right _ _)
  have haomega : a ≤ omega / 6 := (hinner.trans_le (min_le_left _ _)).le
  have hsmall : L * a < epsilon := by
    have hh := (lt_div_iff₀ hL).mp (hinner.trans_le (min_le_right _ _))
    nlinarith
  have hb := hbound a ha (le_min haRho haomega) cap hcap
  exact ⟨hb.1, hb.2.trans_lt hsmall⟩

theorem tendsto_corrected_smallRemainder_limsup_cutoff_zero
    (D : HistoricalPrefixCapData) (J : Finset (FifthLabel D.m))
    (e : ℚ) (chi omega : ℝ) (homega : 0 < omega)
    (rows : Finset ProducerRow) (licensed : ProducerRow → Prop)
    (howned : P1VariableFifthSelectedStoredBinding.OriginalOwnedRows D J e chi omega)
    (hcheck : storedH45Check D J e rows = true) (cap : ℕ → ℕ)
    (hcap : ∀ᶠ N : ℕ in evenTargets, (N : ℝ) ^ (19 / 96 : ℝ) ≤ (cap N : ℝ)) :
    Tendsto (fun a : ℝ => limsup (fun N : ℕ =>
      |P1CorrectedFifthGlobalSourceAssembly.smallRemainder
        D J e chi omega rows licensed a N (cap N)|) evenTargets)
      (𝓝[Set.Ioi 0] (0 : ℝ)) (𝓝 0) := by
  apply Metric.tendsto_nhdsWithin_nhds.2
  intro epsilon hepsilon
  obtain ⟨delta, hdelta, hbound⟩ := corrected_smallRemainder_limsup_cutoff_zero
    D J e chi omega homega rows licensed howned hcheck epsilon hepsilon
  refine ⟨delta, hdelta, ?_⟩
  intro a ha hadist
  have ha0 : 0 < a := ha
  have haDelta : a < delta := by
    simpa only [Real.dist_eq, sub_zero, abs_of_pos ha0] using hadist
  obtain ⟨hlo, hhi⟩ := hbound a ha0 haDelta cap hcap
  simpa only [Real.dist_eq, sub_zero, abs_of_nonneg hlo] using hhi

end
end ImbalancedChen.P1CorrectedFifthUniformSmallRemainder
