import ImbalancedChen.P2OriginalSaving16CommonOldPolicy
import ImbalancedChen.P2OriginalFourteenSignedTrimPayment
import ImbalancedChen.FirstExitAdmittedFrontierTuples
import ImbalancedChen.P5PresievedRoughSlotAffineGates

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The actual rank-eight stopped frontier is reindexed, not replaced by an
unordered cube. The original list permutation proves multiplicity one.
The retained14 inclusion is proved by the literal first, third, fifth,
and seventh decisions of policy6 at one schedule chosen before N.
-/
namespace ImbalancedChen.P2OriginalFourteenRetainedTupleOwnership
noncomputable section
open scoped Classical BigOperators
open Set VariableEnvelope
open P2OriginalAscendingEighthCapDictionary
open P2OriginalSaving16FourteenPhysicalAtlas
open P2OriginalSaving16TrimmedHistory
open P2OriginalSaving16CommonOldPolicy
open P5OriginalCommonRefinedConstructor
open P5OriginalCommonRefinedPreservation
open MathlibNt.SieveTheory.LiLiuPrereqWF.SmallRosser

def history (p : Fin 8 → ℕ) : List ℕ := (List.ofFn p).reverse

theorem history_length (p : Fin 8 → ℕ) : (history p).length = 8 := by simp [history]

theorem history_explicit (p : Fin 8 → ℕ) :
    history p = [p 7, p 6, p 5, p 4, p 3, p 2, p 1, p 0] := by
  simp [history, List.ofFn_succ]

theorem tuple_history (p : Fin 8 → ℕ) : primeHistoryTuple 8 (history p) = p := by
  apply List.ofFn_injective
  rw [primeHistoryTuple_ofFn (history_length p)]
  simp only [history, List.reverse_reverse]

theorem history_log (N : ℕ) (p : Fin 8 → ℕ) :
    primeHistoryLogCoordinates (N : ℝ) 8 (history p) = actualPrimeTupleLog N p := by
  funext i
  simp only [primeHistoryLogCoordinates, actualPrimeTupleLog, tuple_history]

def tupleCurrent (data : OriginalData) (N : ℕ) (p : Fin 8 → ℕ) : ℝ :=
  lambda6 data (N : ℝ) (rosserAncestor 6 (history p))

def admitted (data : OriginalData) (N cap : ℕ) (z : ℝ) : Finset (Fin 8 → ℕ) :=
  firstExitAdmittedTuples 8 (policy6 data (N : ℝ)) (roughPrimeUniverse N cap 0 z)

/-- Exact multiplicities of the original stopped frontier, before any
restriction to the fourteen cells and before any limit. -/
theorem actual_frontier_tuple_nodup (data : OriginalData) (N cap : ℕ) (z : ℝ) :
    ((firstExitDepthFrontier 8 (policy6 data (N : ℝ))
      (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1 (roughPrimeUniverse N cap 0 z)).map
      (fun state => primeHistoryTuple 8 state.selectedPrefix)).Nodup :=
  firstExitRootFrontier_admitted_tuple_nodup 8 _ _ _ (roughPrimeUniverse_nodup N cap 0 z)

/-- This is the actual signed charge, with its original admission filter.
There is neither a factorial nor an extra summation over cell labels. -/
theorem normalized_charge_eq_admitted_sum
    (data : OriginalData) (N cap : ℕ) (hN : 1 ≤ (N : ℝ)) (z : ℝ) :
    P2OriginalFourteenSignedParentLedger.charge N cap 0 z
        (lambda6 data (N : ℝ)) P4AOriginalAscending14Literal42.literalPattern
        (policy5 data (N : ℝ)) * Real.log (N : ℝ) / singularSeries N =
      ∑ p ∈ admitted data N cap z, (∏ i, 1 / ((p i : ℝ) - 1)) *
        actualPrimeTupleInitialSaving N cap (tupleCurrent data N p)
          (familyNextExponent (N : ℝ) (lambda6 data (N : ℝ))
            P4AOriginalAscending14Literal42.literalPattern (history p)) p := by
  rw [P2OriginalFourteenSignedParentLedger.unpresieved_charge_eq_residual_sum N cap hN]
  have hparent : P4AOriginalEighthParentPhysicalLedger.parentPolicy (N : ℝ)
      (lambda6 data (N : ℝ)) (policy5 data (N : ℝ)) = policy6 data (N : ℝ) := rfl
  rw [hparent]
  let F : List ℕ → ℝ := fun pre =>
    (actualSmallRosserPlusDensity N cap (pre.headD 0 : ℝ)
      (currentLevel (N : ℝ) (lambda6 data (N : ℝ)) pre / (pre.prod : ℝ)) -
     actualSmallRosserPlusDensity N cap (pre.headD 0 : ℝ)
      (familyNextLevel (N : ℝ) (lambda6 data (N : ℝ))
        P4AOriginalAscending14Literal42.literalPattern pre / (pre.prod : ℝ)))
  have he := firstExitRootFrontier_history_sum_eq_admitted_tuple_sum 8
    (policy6 data (N : ℝ)) (fun p : ℕ => 1 / ((p : ℝ) - 1))
    (roughPrimeUniverse N cap 0 z) (roughPrimeUniverse_nodup N cap 0 z) F
  change _ * Real.log (N : ℝ) / singularSeries N = _
  change ((firstExitDepthFrontier 8 _ _ [] true 1 _).map (fun state =>
    (state.selectedPrefix.map (fun q : ℕ => 1 / ((q : ℝ) - 1))).prod *
      F state.selectedPrefix)).sum * _ / _ = _
  rw [he, Finset.sum_mul, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro p hp
  have hprod : (history p).prod = ∏ i, p i := by simp [history]
  have hhead : (history p).headD 0 = p 7 := by rw [history_explicit]; rfl
  simp only [F, history, actualPrimeTupleInitialSaving, tupleCurrent,
    currentLevel, inheritedExponent, familyNextLevel] at hprod hhead ⊢
  rw [hprod, hhead]
  ring

private theorem strictAnti_of_log (N : ℕ) (hN : 1 < N) (p : Fin 8 → ℕ)
    (hp : ∀ i, 0 < p i) (ht : StrictAnti (actualPrimeTupleLog N p)) : StrictAnti p := by
  intro i j hij
  have hr := Real.rpow_lt_rpow_of_exponent_lt (by exact_mod_cast hN) (ht hij)
  rw [actualPrimeTupleLog_rpow hN p hp j, actualPrimeTupleLog_rpow hN p hp i] at hr
  exact_mod_cast hr

private theorem full_third_admissible (N : ℕ) (hN : 1 < N) (p : Fin 8 → ℕ)
    (hp : ∀ i, 0 < p i) (hs : StrictAnti p)
    (planes : Finset (Fin 6) → Bool) (hc : CellGuard planes (actualPrimeTupleLog N p))
    (ell : ℝ) (h1 : 3 * actualPrimeTupleLog N p 0 < ell)
    (h3 : oddCube (actualPrimeTupleLog N p) 2 < ell)
    (h5 : oddCube (actualPrimeTupleLog N p) 4 < ell)
    (h7 : oddCube (actualPrimeTupleLog N p) 6 < ell) :
    ordinaryRosserPrefixAdmissible false ((N : ℝ) ^ ell) (history p) := by
  apply (P5Z.PresievedRoughSlotAffineGates.original_upper_prefix_iff_log hN ell p hp hs).mpr
  let t := actualPrimeTupleLog N p
  have hS : S t < oddCube t 6 := by
    have h67 := hc.order (by decide : (6 : Fin 8) < 7)
    have hpos := hc.coordinate_pos 6
    norm_num [S, oddCube, prefixSum, Finset.sum_filter, Fin.sum_univ_succ] at *
    linarith
  refine ⟨hS.trans h7, ?_⟩
  intro i hi
  fin_cases i
  · simpa [P5Z.PresievedRoughSlotAffineGates.cube, P5Z.PresievedRoughSlotAffineGates.prefix,
      oddCube, prefixSum] using h1
  · norm_num at hi
  · simpa only [P5Z.PresievedRoughSlotAffineGates.cube,
      P5Z.PresievedRoughSlotAffineGates.prefix, oddCube, prefixSum, Fin.lt_def] using h3
  · norm_num at hi
  · simpa only [P5Z.PresievedRoughSlotAffineGates.cube,
      P5Z.PresievedRoughSlotAffineGates.prefix, oddCube, prefixSum, Fin.lt_def] using h5
  · norm_num at hi
  · simpa only [P5Z.PresievedRoughSlotAffineGates.cube,
      P5Z.PresievedRoughSlotAffineGates.prefix, oddCube, prefixSum, Fin.lt_def] using h7
  · norm_num at hi

private theorem ancestor_admissible (Q : ℝ) (p : Fin 8 → ℕ)
    (hp : ∀ i, Nat.Prime (p i)) (hs : StrictAnti p)
    (hfull : ordinaryRosserPrefixAdmissible false Q (history p)) (k : ℕ) :
    ordinaryRosserPrefixAdmissible false Q (rosserAncestor k (history p)) := by
  have hprime : ∀ q ∈ history p, Nat.Prime q := by
    intro q hq
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp (List.mem_reverse.mp hq)
    exact hp i
  have hsort : (history p).Pairwise (· < ·) := by
    simpa only [history, List.pairwise_reverse] using List.pairwise_ofFn.mpr hs
  have he : (history p).take ((history p).length - k) ++ rosserAncestor k (history p) =
      history p := List.take_append_drop _ _
  exact ordinaryRosserPrefixAdmissible_of_append false Q _ _
    (by simpa only [he] using hprime) (by simpa only [he] using hsort)
    (by simpa only [he] using hfull)

/-- Retained actual14 tuples pass every original policy test. The only
inputs here are explicit arithmetic cube inequalities and the original
firstStop; the public schedule theorem below derives all of them from K. -/
private theorem policy6_valid_from_source_history
    (data : OriginalData) (N : ℕ) (hN : 1 < N) (he : 0 < data.e)
    (hesmall : (data.e : ℝ) < 1 / 1000) (p : Fin 8 → ℕ)
    (hp : ∀ i, Nat.Prime (p i)) (c : Cell)
    (hc : sourceRows c (actualPrimeTupleLog N p))
    (hstop : HistoricalThirdCoarse.firstStop (data.e : ℝ) data.m (N : ℝ)
      (rosserAncestor 1 (history p)))
    (h1 : 3 * actualPrimeTupleLog N p 0 < lambda3 data (N : ℝ) (rosserAncestor 4 (history p)))
    (h3 : oddCube (actualPrimeTupleLog N p) 2 < lambda3 data (N : ℝ) (rosserAncestor 4 (history p)))
    (h5 : oddCube (actualPrimeTupleLog N p) 4 < lambda3 data (N : ℝ) (rosserAncestor 4 (history p)))
    (h7 : oddCube (actualPrimeTupleLog N p) 6 < lambda3 data (N : ℝ) (rosserAncestor 4 (history p)))
    (h36 : lambda3 data (N : ℝ) (rosserAncestor 4 (history p)) ≤ tupleCurrent data N p) :
    FirstExitValidSelection (policy6 data (N : ℝ)) [] true (List.ofFn p) := by
  have hg := sourceRows_cellGuard c _ hc
  have hs := strictAnti_of_log N hN p (fun i => (hp i).pos) hg.order
  have hfull := full_third_admissible N hN p (fun i => (hp i).pos) hs _ hg _ h1 h3 h5 h7
  have had3 := ancestor_admissible _ p hp hs hfull 3
  have had5 := ancestor_admissible _ p hp hs hfull 5
  have had7 := ancestor_admissible _ p hp hs hfull 7
  have hseed : originalSeed data (N : ℝ) (rosserAncestor 3 (history p)) =
      lambda3 data (N : ℝ) (rosserAncestor 4 (history p)) := by
    have hh := actual_third_eq_original data (N : ℝ) (history p) (history_length p) c
      (by simpa only [history_log] using hc)
    simpa only [originalSeed, P1OriginalVariableFourthContinuation.seedExponent,
      rosserAncestor_nested 3 3 le_rfl] using hh.symm
  have h35 := lambda3_le_exponent5 data (N : ℝ) (rosserAncestor 5 (history p))
  rw [lambda3_ancestor data (N : ℝ) 5 (by decide),
    ← lambda3_ancestor data (N : ℝ) 4 (by decide) (history p)] at h35
  have had5' := ordinaryRosserPrefixAdmissible_mono false _
    (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN.le) h35) had5
  have had7' := ordinaryRosserPrefixAdmissible_mono false _
    (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN.le) h36) had7
  have hinit : 3 * actualPrimeTupleLog N p 0 < HistoricalThirdCoarse.initial (data.e : ℝ) := by
    have hx := hg.largest
    norm_num [HistoricalThirdCoarse.initial, extendedDistributionCap, mu] at hx ⊢
    linarith
  have hcube : (p 0 : ℝ) ^ 3 < (N : ℝ) ^ HistoricalThirdCoarse.initial (data.e : ℝ) := by
    have hh := Real.rpow_lt_rpow_of_exponent_lt (by exact_mod_cast hN) hinit
    rw [mul_comm (3 : ℝ), Real.rpow_mul (by positivity : (0 : ℝ) ≤ N),
      Real.rpow_natCast, actualPrimeTupleLog_rpow hN p (fun i => (hp i).pos) 0] at hh
    exact hh
  have hprod : (p 0 : ℝ) < (N : ℝ) ^ HistoricalThirdCoarse.initial (data.e : ℝ) := by
    have hp0 : (1 : ℝ) < p 0 := by exact_mod_cast (hp 0).one_lt
    nlinarith
  have had1 : ordinaryRosserPrefixAdmissible false
      ((N : ℝ) ^ HistoricalThirdCoarse.initial (data.e : ℝ)) [p 0] := by
    simpa [ordinaryRosserPrefixAdmissible, UpperAdmissibleSet,
      Finset.filter_singleton, pow_succ, mul_comm] using And.intro hprod hcube
  have hfirst : policy6 data (N : ℝ) false [p 0] = true := by
    simp only [policy6, policy5, firstExitDepthSplicePolicy, List.length_singleton,
      if_pos (by decide : 1 ≤ 6), if_pos (by decide : 1 ≤ 4)]
    rw [common3_through_two data (N : ℝ) false [p 0] (by simp)]
    have hs1 : HistoricalThirdCoarse.firstStop (data.e : ℝ) data.m (N : ℝ) [p 0] := by
      simpa [history_explicit, rosserAncestor] using hstop
    simp [old3, HistoricalThirdCoarse.policy_through_two, HistoricalThirdCoarse.initialPolicy,
      oddFirstExitPolicy, had1, hs1]
  have hthird : policy6 data (N : ℝ) false [p 2, p 1, p 0] = true := by
    change common3 data (N : ℝ) false [p 2, p 1, p 0] = true
    unfold common3
    apply Bool.or_eq_true.mpr
    left
    rw [old3_after_two data (N : ℝ) false _ (by simp)]
    have had3' : ordinaryRosserPrefixAdmissible false
        ((N : ℝ) ^ originalSeed data (N : ℝ) (rosserAncestor 3 (history p)))
        (rosserAncestor 3 (history p)) := by rwa [hseed]
    have hh : ordinaryRosserPrefixAdmissible false
        ((N : ℝ) ^ originalSeed data (N : ℝ) [p 2, p 1, p 0]) [p 2, p 1, p 0] := by
      simpa [history_explicit, rosserAncestor] using had3'
    simp [ordinaryParityRosserPolicy, oddFirstExitPolicy, hh]
  have hfifth : policy6 data (N : ℝ) false [p 4, p 3, p 2, p 1, p 0] = true := by
    simpa [policy6, policy5, firstExitDepthSplicePolicy, frozenParityRosserPolicy,
      ancestorFrozenPolicy, ordinaryParityRosserPolicy, oddFirstExitPolicy, level5,
      history_explicit, rosserAncestor] using had5'
  have hseventh : policy6 data (N : ℝ) false [p 6, p 5, p 4, p 3, p 2, p 1, p 0] = true := by
    simpa [policy6_rank_seven, tupleCurrent, history_explicit, rosserAncestor] using had7'
  simpa [List.ofFn_succ, FirstExitValidSelection, policy6_even, hfirst, hthird,
    hfifth, hseventh]

theorem exists_retained_tuple_ownership (delta : ℝ) (hdelta : 0 < delta) :
    ∃ e0 : ℝ, 0 < e0 ∧ ∀ e : ℚ, 0 < e → (e : ℝ) < e0 →
      ∀ chi : ℝ, 0 < chi → chi ≤ (e : ℝ) / 10 →
      ∃ m0 : ℕ, ∀ data : OriginalData, data.e = e → data.chi = chi → m0 ≤ data.m →
      data.omega ≤ 1 / 100 → ∀ N cap : ℕ, 1 < N → (N : ℝ) ^ mu ≤ (cap : ℝ) →
      ∀ p ∈ actualPrimeBoxTuples N (fun _ : Fin 8 => cutoff) (fun _ => mu),
        actualPrimeTupleLog N p ∈ trimmedRegion delta →
        p ∈ admitted data N cap ((N : ℝ) ^ mu) ∧
          CurrentParentGuard (actualPrimeTupleLog N p) (tupleCurrent data N p) := by
  obtain ⟨e0, he0, hparent⟩ := exists_common_actual_parent_on_trim delta hdelta
  refine ⟨min e0 (1 / 1000), lt_min he0 (by norm_num), ?_⟩
  intro e he hee chi hchi hchie
  obtain ⟨m0, hm0⟩ := hparent e he (hee.trans_le (min_le_left _ _)) chi hchi hchie
  refine ⟨m0, ?_⟩
  intro data hde hdc hdm homega N cap hN hcap p hp ht
  have hpi := mem_actualPrimeBoxTuples_iff.mp hp
  have hpos : ∀ q ∈ history p, 0 < q := by
    intro q hq
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp (List.mem_reverse.mp hq)
    exact (hpi i).1.pos
  have hreal : (1 : ℝ) < N := by exact_mod_cast hN
  obtain ⟨hstop, hsupp, h1, h3, h5, h7, h36, hguard, hgain⟩ :=
    hm0 data hde hdc hdm homega (N : ℝ) hreal (history p) (history_length p) hpos
      (by simpa only [history_log] using ht)
  simp only [history_log] at h1 h3 h5 h7 hguard
  obtain ⟨c, hc⟩ := mem_iUnion.mp (trimmedRegion_subset_region delta hdelta ht)
  have hvalid := policy6_valid_from_source_history data N hN (by simpa only [hde] using he)
    (by simpa only [hde] using hee.trans_le (min_le_right _ _)) p
    (fun i => (hpi i).1) c hc hstop h1 h3 h5 h7 h36
  refine ⟨?_, hguard⟩
  apply (mem_actualPrimeAdmittedTuples_iff_of_cutoff_le_cap 8 _ N cap 0 _ hcap p).mpr
  refine ⟨strictAnti_of_log N hN p (fun i => (hpi i).1.pos)
    (sourceRows_cellGuard c _ hc).order, ?_, hvalid⟩
  intro i
  exact ⟨(hpi i).1, (hpi i).2.1, Nat.cast_nonneg _, (hpi i).2.2.2⟩

end
end ImbalancedChen.P2OriginalFourteenRetainedTupleOwnership
