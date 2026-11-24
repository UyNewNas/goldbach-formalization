import ImbalancedChen.P4AOriginalFull87SevenCubeAdmission
import ImbalancedChen.P4AOriginalFull87ActualCommonHistory
import ImbalancedChen.P1ActualFrontierReverseAdmission

/-!
SOURCE ONLY / UNCOMPILED / NO KERNEL CREDIT.
Every odd decision is checked at its ACTUAL own-rank level. The ordinary
third level is not silently replaced by the larger final sixth level.
The terminal in the next file supplies RealizedHistory internally from the
unchanged original archive schedule; this file is the finite conversion.
-/
namespace ImbalancedChen.P4AOriginalFull87PolicyReverseAdmission
noncomputable section
open scoped Classical BigOperators
open VariableEnvelope
open P4AOriginalFull87SourceDictionary
open P4AOriginalFull87SevenCubeAdmission
open P4AOriginalFull87ActualCommonHistory
open P5OriginalCommonRefinedConstructor P5OriginalCommonRefinedPreservation
open P4AOriginalCompleteSixthChronology

/-- Original low decisions survive both concrete later splices. -/
theorem low_approval (e : ℚ) (q : ℕ) (omega N : ℝ) (xs : List ℕ)
    (hl : xs.length ≤ 4)
    (ho : old3 (data e q omega) N false xs = true) :
    P4AOriginalFull87CompleteSixthDispatch.policy e q omega N false xs = true := by
  rw [P4AOriginalFull87CompleteSixthDispatch.policy_through_eight
    e q omega N false xs (by omega),
    current_policy_through_six e q omega N false xs (by omega)]
  simp only [policy5, firstExitDepthSplicePolicy, if_pos hl]
  simp only [common3, ho, Bool.true_or]

/-- Four original odd-history bounds yield all eight literal policy
approvals. Even ranks are retained by the exact concrete policy theorem. -/
theorem validSelection_of_realized_history
    (e : ℚ) (q : ℕ) (omega N : ℝ) (he : 0 ≤ e) (hN : 1 < N)
    (p : Fin 8 → ℕ) (hp : ∀ i, (p i).Prime) (c : Cell)
    (hs : Source c (point N p))
    (hr : RealizedHistory e q omega N (pre p) c) :
    FirstExitValidSelection
      (P4AOriginalFull87CompleteSixthDispatch.policy e q omega N) [] true
      (pre p).reverse := by
  let d := data e q omega
  let L := lambda3 d N (rosserAncestor 4 (pre p))
  have heR : (0 : ℝ) ≤ d.e := by exact_mod_cast he
  have hpos : ∀ i, 0 < p i := fun i => (hp i).pos
  have hord := source_strictAnti N hN p hpos c hs
  have hsort7 : [p 6, p 5, p 4, p 3, p 2, p 1, p 0].Pairwise (· < ·) :=
    (List.pairwise_cons.mp (pre_pairwise p hord)).2
  have hprime7 : ∀ r ∈ [p 6, p 5, p 4, p 3, p 2, p 1, p 0], r.Prime := by
    intro r h
    simp only [List.mem_cons, List.mem_singleton] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact hp _
  have hadm7 : ordinaryRosserPrefixAdmissible false (N^L)
      [p 6, p 5, p 4, p 3, p 2, p 1, p 0] :=
    seven_admissible_of_histories N hN p hpos hord L hr.2.2.1
  have hadm5 : ordinaryRosserPrefixAdmissible false (N^L)
      [p 4, p 3, p 2, p 1, p 0] :=
    ordinaryRosserPrefixAdmissible_of_append false (N^L) [p 6, p 5]
      [p 4, p 3, p 2, p 1, p 0] hprime7 hsort7 hadm7
  have hadm3 : ordinaryRosserPrefixAdmissible false (N^L) [p 2, p 1, p 0] :=
    ordinaryRosserPrefixAdmissible_of_append false (N^L) [p 6, p 5, p 4, p 3]
      [p 2, p 1, p 0] hprime7 hsort7 hadm7
  have hadm1 : ordinaryRosserPrefixAdmissible false (N^L) [p 0] :=
    ordinaryRosserPrefixAdmissible_of_append false (N^L)
      [p 6, p 5, p 4, p 3, p 2, p 1] [p 0] hprime7 hsort7 hadm7
  have hsupport : P1ThirdFallbackSupport.supported (d.e : ℝ) d.chi d.m
      d.omega N (rosserAncestor 3 (pre p)) := hr.2.1
  have hL : L = P1CoarseFirstCubeFallbackMargin.effectiveExponent
      (d.e : ℝ) d.chi d.m d.omega N (rosserAncestor 3 (pre p)) :=
    P4AOriginalFull87CompleteSixthBound.actual_third_eq_original
      d N (pre p) (pre_length p) c hs
  have hLinitial : L < HistoricalThirdCoarse.initial (d.e : ℝ) := by
    obtain ⟨j, hj, ht⟩ := hsupport.2
    rw [hL, P1CoarseFirstCubeFallbackMargin.effectiveExponent, if_pos hsupport,
      HistoricalThirdCoarse.exponent_on_cell _ _ _ _ j hj ht]
    have hjfacts := (HistoricalThirdCoarse.mem_cells _ _ _ _).mp hj
    exact HistoricalThirdCoarse.levelExponent_lt_initial _ _ heR hjfacts.1 hjfacts.2.1
  have hfirst : ordinaryRosserPrefixAdmissible false
      (N ^ HistoricalThirdCoarse.initial (d.e : ℝ)) [p 0] :=
    ordinaryRosserPrefixAdmissible_mono false [p 0]
      (Real.rpow_le_rpow_of_exponent_le hN.le hLinitial.le) hadm1
  have hstop : HistoricalThirdCoarse.firstStop (d.e : ℝ) d.m N [p 0] := by
    simpa only [pre, rosserAncestor, List.length_cons, List.length_nil,
      List.drop_succ_cons, List.drop_zero] using hr.1
  have hfirstOld : old3 d N false [p 0] = true := by
    change HistoricalThirdCoarse.policy (d.e : ℝ) d.chi d.m d.omega N false [p 0] = true
    rw [HistoricalThirdCoarse.policy_through_two _ _ _ _ _ _ _ (by simp)]
    simp [HistoricalThirdCoarse.initialPolicy, oddFirstExitPolicy, hfirst, hstop]
  have hseed : originalSeed d N [p 2, p 1, p 0] = L := by
    rw [hL]
    simp [originalSeed, P1OriginalVariableFourthContinuation.seedExponent,
      pre, rosserAncestor]
  have hthirdOld : old3 d N false [p 2, p 1, p 0] = true := by
    rw [old3_after_two d N false _ (by simp), hseed]
    simpa only [ordinaryParityRosserPolicy, Bool.false_eq_true, if_false,
      oddFirstExitPolicy, Bool.false_or, decide_eq_true_eq] using hadm3
  have hL5 : L ≤ exponent5 d N [p 4, p 3, p 2, p 1, p 0] := by
    have h := lambda3_le_exponent5 d N (rosserAncestor 5 (pre p))
    rw [lambda3_ancestor d N 5 (by decide) (pre p)] at h
    dsimp only [L]
    rw [lambda3_ancestor d N 4 (by decide) (pre p)]
    simpa [pre, rosserAncestor] using h
  have hadm5actual : ordinaryRosserPrefixAdmissible false
      (N ^ exponent5 d N [p 4, p 3, p 2, p 1, p 0]) [p 4, p 3, p 2, p 1, p 0] :=
    ordinaryRosserPrefixAdmissible_mono false _
      (Real.rpow_le_rpow_of_exponent_le hN.le hL5) hadm5
  have hadm7actual : ordinaryRosserPrefixAdmissible false
      (N ^ currentSixthExponent e q omega N (rosserAncestor 6 (pre p)))
      [p 6, p 5, p 4, p 3, p 2, p 1, p 0] :=
    ordinaryRosserPrefixAdmissible_mono false _
      (Real.rpow_le_rpow_of_exponent_le hN.le hr.2.2.2.1) hadm7
  have htest1 := low_approval e q omega N [p 0] (by simp) hfirstOld
  have htest3 := low_approval e q omega N [p 2, p 1, p 0] (by simp) hthirdOld
  have htest5 : P4AOriginalFull87CompleteSixthDispatch.policy e q omega N false
      [p 4, p 3, p 2, p 1, p 0] = true := by
    rw [P4AOriginalFull87CompleteSixthDispatch.policy_through_eight
      e q omega N false _ (by simp),
      current_policy_through_six e q omega N false _ (by simp)]
    simpa [policy5, firstExitDepthSplicePolicy, frozenParityRosserPolicy,
      ancestorFrozenPolicy, ordinaryParityRosserPolicy, oddFirstExitPolicy,
      level5, rosserAncestor, d] using hadm5actual
  have htest7 : P4AOriginalFull87CompleteSixthDispatch.policy e q omega N false
      [p 6, p 5, p 4, p 3, p 2, p 1, p 0] = true := by
    rw [P4AOriginalFull87CompleteSixthDispatch.policy_through_eight
      e q omega N false _ (by simp),
      current_policy_after_six e q omega N false _ (by simp)]
    simpa [ordinaryParityRosserPolicy, oddFirstExitPolicy, pre, rosserAncestor]
      using hadm7actual
  simp only [pre, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.append_assoc, List.singleton_append, FirstExitValidSelection,
    Bool.not_true, Bool.not_false]
  exact ⟨htest1, P4AOriginalFull87CompleteSixthDispatch.policy_even e q omega N _,
    htest3, P4AOriginalFull87CompleteSixthDispatch.policy_even e q omega N _,
    htest5, P4AOriginalFull87CompleteSixthDispatch.policy_even e q omega N _,
    htest7, P4AOriginalFull87CompleteSixthDispatch.policy_even e q omega N _, trivial⟩

/-- The raw original source proves the endpoint bounds for every actual
label, including the source's literal last-coordinate floor. -/
theorem source_carrier_bounds (N : ℝ) (hN : 1 < N) (p : Fin 8 → ℕ)
    (hp : ∀ i, 0 < p i) (c : Cell) (hs : Source c (point N p))
    (w z : ℝ) (hw : w ≤ N ^ (53 / 13824 : ℝ)) (hz : N^mu ≤ z) :
    ∀ i, w ≤ (p i : ℝ) ∧ (p i : ℝ) < z := by
  have ht : StrictAnti (point N p) :=
    Fin.strictAnti_iff_succ_lt.mpr (source_basic hs).2.2.2
  intro i
  have hlo : (53 / 13824 : ℝ) < point N p i :=
    (source_basic hs).2.2.1.trans_le (ht.antitone (show i ≤ 7 by omega))
  have hhi : point N p i < mu :=
    (ht.antitone (show (0 : Fin 8) ≤ i by omega)).trans_lt (source_basic hs).1
  constructor
  · have h := (Real.rpow_lt_rpow_of_exponent_lt hN hlo).le
    rw [point_rpow N hN p hp] at h
    exact hw.trans h
  · have h := Real.rpow_lt_rpow_of_exponent_lt hN hhi
    rw [point_rpow N hN p hp] at h
    exact h.trans_le hz

end
end ImbalancedChen.P4AOriginalFull87PolicyReverseAdmission
