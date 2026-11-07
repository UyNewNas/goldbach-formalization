import ImbalancedChen.ActualHistoricalThirdTupleDictionary
import ImbalancedChen.FirstExitAdmittedFrontierTuples
import ImbalancedChen.PrimeHistoryLogCoordinates

/-!
# P1: fourth admitted tuples for the original coarse third policy

The parent is literally HistoricalThirdCoarse.policy, with initialPolicy and
its firstStop.  Selected third cells retain the initial first cube, the current
third level's own first cube, the third cube, and inclusive rough activation.
The fourth selection is inactive.  No ordinary-base D policy is substituted.
The two cell meshes may differ; the same-mesh specialization is also supplied.
-/

namespace ImbalancedChen
noncomputable section
open scoped Classical List BigOperators
open Set

namespace HistoricalThirdCoarse.P1OriginalFourth

/-- The oldest three processing coordinates of a fourth tuple. -/
def prefix3 {α : Type*} (p : Fin 4 → α) : Fin 3 → α :=
  historicalPrefixProject (by omega : 3 ≤ 4) p

def history3 (p : Fin 4 → ℕ) : List ℕ := P1ActualTuple.history (prefix3 p)
def history4 (p : Fin 4 → ℕ) : List ℕ := [p 3, p 2, p 1, p 0]

theorem prefix3_log (N : ℕ) (p : Fin 4 → ℕ) :
    prefix3 (actualPrimeTupleLog N p) = actualPrimeTupleLog N (prefix3 p) := by rfl

theorem history3_log (N : ℕ) (p : Fin 4 → ℕ) :
    primeHistoryLogCoordinates (N : ℝ) 3 (history3 p) = prefix3 (actualPrimeTupleLog N p) := by
  exact P1ActualTuple.history_log N (prefix3 p)

theorem history4_log (N : ℕ) (p : Fin 4 → ℕ) :
    primeHistoryLogCoordinates (N : ℝ) 4 (history4 p) = actualPrimeTupleLog N p := by
  funext i
  fin_cases i <;> rfl

/-- The original initial rank-one stop remains an explicit logarithmic row
condition, including its original half-open first-label ownership. -/
def firstStopRegion (e : ℝ) (m : ℕ) : Set (Fin 4 → ℝ) :=
  {t | ∃ i : Fin (m + 1),
    logPrimeMeshPoint 0 (19 / 96) m i.val ≤ t 0 ∧
    t 0 < logPrimeMeshPoint 0 (19 / 96) m (i.val + 1) ∧
    logPrimeMeshPoint 0 (19 / 96) m (i.val + 1) ≤ VariableEnvelope.extendedFirstStop - 4 * e}

theorem firstStop_iff_log (e : ℝ) (m N : ℕ) (p : Fin 4 → ℕ) :
    firstStop e m (N : ℝ) [p 0] ↔ actualPrimeTupleLog N p ∈ firstStopRegion e m := by
  simp [firstStop, firstStopRegion, primeHistoryLogCoordinates,
    primeHistoryTuple, actualPrimeTupleLog]

/-- Exact rank-four full validity of the actual original policy. -/
theorem valid_fourth_iff (e chi : ℝ) (m : ℕ) (omega N : ℝ)
    (p : Fin 4 → ℕ) (hpos : ∀ i, 0 < p i) (hs : StrictAnti p) :
    FirstExitValidSelection (policy e chi m omega N) [] true (List.ofFn p) ↔
      (p 0 : ℝ) ^ 3 < N ^ initial e ∧ firstStop e m N [p 0] ∧
        (p 0 : ℝ) ^ 3 < rawLevel e chi m omega N (history3 p) ∧
        (p 0 : ℝ) * p 1 * (p 2 : ℝ) ^ 3 < rawLevel e chi m omega N (history3 p) := by
  have hv : FirstExitValidSelection (policy e chi m omega N) [] true (List.ofFn p) ↔
      FirstExitValidSelection (policy e chi m omega N) [] true (List.ofFn (prefix3 p)).dropLast ∧
        policy e chi m omega N false (history3 p) = true := by
    simp [List.ofFn_succ, FirstExitValidSelection, prefix3, historicalPrefixProject,
      history3, P1ActualTuple.history, policy_even, and_assoc]
  have hparent : FirstExitValidSelection (policy e chi m omega N) [] true
      (List.ofFn (prefix3 p)).dropLast ↔
      (p 0 : ℝ) ^ 3 < N ^ initial e ∧ firstStop e m N [p 0] := by
    simpa only [prefix3, historicalPrefixProject] using
      P1ActualTuple.parent_two_iff e chi m omega N (prefix3 p) (hpos 0)
  rw [hv, hparent]
  have hthird := policy_third_iff e chi m omega N (p 0) (p 1) (p 2) (hpos 2)
    (hs (by decide : (1 : Fin 4) < 2)) (hs (by decide : (0 : Fin 4) < 1))
  have hh : history3 p = [p 2, p 1, p 0] := by rfl
  rw [hh, hthird]
  tauto

/-- Even fourth admission retains every candidate of the actual rank-three
coarse parent, with no replacement of its initial first-label stop. -/
theorem candidates_eq_admitted (e chi : ℝ) (m : ℕ) (omega N : ℝ) (carrier : List ℕ) :
    firstExitFrontierTuples 3 (policy e chi m omega N) carrier =
      firstExitAdmittedTuples 4 (policy e chi m omega N) carrier := by
  ext p
  rw [mem_firstExitFrontierTuples_iff, mem_firstExitAdmittedTuples_iff]
  apply and_congr_right
  intro _hsub
  simp [List.ofFn_succ, FirstExitValidSelection, policy_even]

/-- Three order rows and all three original cube rows. -/
def gateForms : Fin 6 → (Fin 4 → ℝ) →L[ℝ] ℝ :=
  let e (i : Fin 4) : (Fin 4 → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj i
  ![e 1 - e 0, e 2 - e 1, e 3 - e 2,
    (3 : ℝ) • e 0, (3 : ℝ) • e 0, e 0 + e 1 + (3 : ℝ) • e 2]

def gateBounds (initial third : ℝ) : Fin 6 → ℝ := ![0, 0, 0, initial, third, third]

theorem gateForms_ne_zero : ∀ i, gateForms i ≠ 0 := by
  intro i h
  have hh := congrArg (fun L : (Fin 4 → ℝ) →L[ℝ] ℝ => L (fun i => (i.val : ℝ) + 1)) h
  fin_cases i <;> norm_num [gateForms] at hh

theorem mem_gateRegion (initial third : ℝ) (t : Fin 4 → ℝ) :
    t ∈ primeAffineGateRegion gateForms (gateBounds initial third) ↔
      StrictAnti t ∧ 3 * t 0 < initial ∧ 3 * t 0 < third ∧
        t 0 + t 1 + 3 * t 2 < third := by
  have ha : StrictAnti t ↔ t 1 < t 0 ∧ t 2 < t 1 ∧ t 3 < t 2 := by
    constructor
    · intro h
      exact ⟨h (by decide), h (by decide), h (by decide)⟩
    · rintro ⟨h1, h2, h3⟩
      apply Fin.strictAnti_iff_succ_lt.mpr
      intro i
      fin_cases i
      · exact h1
      · exact h2
      · exact h3
  simp only [ha]
  simp [primeAffineGateRegion, gateForms, gateBounds, Fin.forall_fin_succ, and_assoc]

/-- All actual coarse-parent tests survive on the fourth tuple. -/
def jointRegion (e omega : ℝ) (m : ℕ) (j3 : Cell m) : Set (Fin 4 → ℝ) :=
  (primeAffineGateRegion gateForms (gateBounds (initial e) (levelExponent e (box m j3))) ∩
    firstStopRegion e m) ∩ {t | omega ≤ t 2}

/-- The original joint region proves the old fourth PLUS gate strictly. -/
theorem jointRegion_strict_plus (e omega : ℝ) (m : ℕ) (j3 : Cell m)
    (t : Fin 4 → ℝ) (ht : t ∈ jointRegion e omega m j3) :
    (∑ i, t i) + t 3 < levelExponent e (box m j3) := by
  have hg := (mem_gateRegion _ _ _).mp ht.1.1
  have h32 : t 3 < t 2 := hg.1 (by decide : (2 : Fin 4) < 3)
  have hsum : (∑ i, t i) = t 0 + t 1 + t 2 + t 3 := by
    simp [Fin.sum_univ_succ, add_assoc]
  rw [hsum]
  linarith [hg.2.2.2]

/-- Both original and raised fourth PLUS residuals are legal at positive
terminal coordinate; no initial-versus-third cap comparison is assumed. -/
theorem jointRegion_plus_legal (e omega : ℝ) (m : ℕ) (j3 : Cell m)
    (t : Fin 4 → ℝ) (ht : t ∈ jointRegion e omega m j3) (ht3 : 0 < t 3)
    (lambda : ℝ) (hlevel : levelExponent e (box m j3) ≤ lambda) :
    0 < t 3 ∧ t 3 < lambda - ∑ i, t i ∧ 1 < (lambda - ∑ i, t i) / t 3 := by
  have hgate := jointRegion_strict_plus e omega m j3 t ht
  have hquot : t 3 < lambda - ∑ i, t i := by linarith
  exact ⟨ht3, hquot, (one_lt_div ht3).mpr hquot⟩

theorem firstStopRegion_measurable (e : ℝ) (m : ℕ) : MeasurableSet (firstStopRegion e m) := by
  have heq : firstStopRegion e m = ⋃ i : Fin (m + 1),
      {t : Fin 4 → ℝ | logPrimeMeshPoint 0 (19 / 96) m i.val ≤ t 0 ∧
        t 0 < logPrimeMeshPoint 0 (19 / 96) m (i.val + 1) ∧
        logPrimeMeshPoint 0 (19 / 96) m (i.val + 1) ≤ VariableEnvelope.extendedFirstStop - 4 * e} := by
    ext t
    simp only [firstStopRegion, Set.mem_setOf_eq, Set.mem_iUnion]
  rw [heq]
  apply MeasurableSet.iUnion
  intro i
  have hbase : MeasurableSet {t : Fin 4 → ℝ |
      logPrimeMeshPoint 0 (19 / 96) m i.val ≤ t 0 ∧
        t 0 < logPrimeMeshPoint 0 (19 / 96) m (i.val + 1)} :=
    (isClosed_le continuous_const (continuous_apply 0)).measurableSet.inter
      (isOpen_lt (continuous_apply 0) continuous_const).measurableSet
  by_cases hs : logPrimeMeshPoint 0 (19 / 96) m (i.val + 1) ≤
      VariableEnvelope.extendedFirstStop - 4 * e
  · simpa only [hs, and_true] using hbase
  · simp only [hs, and_false, Set.setOf_false]
    exact MeasurableSet.empty

theorem jointRegion_measurable (e omega : ℝ) (m : ℕ) (j3 : Cell m) :
    MeasurableSet (jointRegion e omega m j3) := by
  exact ((measurableSet_primeAffineGateRegion gateForms _).inter
    (firstStopRegion_measurable e m)).inter
      (isClosed_le continuous_const (continuous_apply 2)).measurableSet
/-- Genuine cross-mesh intersection; no endpoint alignment is assumed. -/
def jointCell (m n : ℕ) (j3 : Cell m) (j4 : Fin 4 → Fin (n + 1)) : Set (Fin 4 → ℝ) :=
  logPrimeMeshCell 0 (19 / 96) n j4 ∩
    prefix3 ⁻¹' logPrimeMeshCell 0 (19 / 96) m j3

theorem jointCell_measurable (m n : ℕ) (j3 : Cell m) (j4 : Fin 4 → Fin (n + 1)) :
    MeasurableSet (jointCell m n j3 j4) := by
  have hprefix : Continuous (prefix3 : (Fin 4 → ℝ) → (Fin 3 → ℝ)) :=
    continuous_pi (fun _ => continuous_apply _)
  exact (measurableSet_logPrimeMeshCell 0 (19 / 96) n j4).inter
    ((measurableSet_logPrimeMeshCell 0 (19 / 96) m j3).preimage hprefix.measurable)
theorem rough_on_jointCell (m n : ℕ) (omega : ℝ)
    (j3 : Cell m) (j4 : Fin 4 → Fin (n + 1))
    (hwhole : omega ≤ logPrimeMeshLo 0 (19 / 96) m j3 2)
    (t : Fin 4 → ℝ) (ht : t ∈ jointCell m n j3 j4) : omega ≤ t 2 := by
  exact hwhole.trans (mem_logPrimeMeshCell.mp ht.2 2).1

/-- On a whole-active selected third cell the true raw Q3 is constant,
independently of any future fourth replacement cap. -/
theorem rawLevel_on_selected_jointCell
    (e chi : ℝ) (m n : ℕ) (omega : ℝ) (N : ℕ) (hN : 1 < N)
    (p : Fin 4 → ℕ) (hpos : ∀ i, 0 < p i)
    (j3 : Cell m) (hj3 : j3 ∈ cells e chi m) (j4 : Fin 4 → Fin (n + 1))
    (hwhole : omega ≤ logPrimeMeshLo 0 (19 / 96) m j3 2)
    (ht : actualPrimeTupleLog N p ∈ jointCell m n j3 j4) :
    rawLevel e chi m omega (N : ℝ) (history3 p) =
      (N : ℝ) ^ levelExponent e (box m j3) := by
  have hrough := rough_on_jointCell m n omega j3 j4 hwhole _ ht
  have hactive := (P1ActualTuple.active_iff_log hN omega (prefix3 p)
    (fun i => hpos ⟨i.val, by omega⟩)).mpr hrough
  have ht3 : primeHistoryLogCoordinates (N : ℝ) 3 (history3 p) ∈
      logPrimeMeshCell 0 (19 / 96) m j3 := by
    rw [history3_log]
    exact ht.2
  exact rawLevel_on_cell e chi m omega (N : ℝ) (history3 p) hactive j3 hj3 ht3

private theorem cube_tests_iff_log {N : ℕ} (hN : 1 < N) (initial third : ℝ)
    (p : Fin 4 → ℕ) (hpos : ∀ i, 0 < p i) :
    ((p 0 : ℝ) ^ 3 < (N : ℝ) ^ initial ∧
      (p 0 : ℝ) ^ 3 < (N : ℝ) ^ third ∧
      (p 0 : ℝ) * p 1 * (p 2 : ℝ) ^ 3 < (N : ℝ) ^ third) ↔
      3 * actualPrimeTupleLog N p 0 < initial ∧
        3 * actualPrimeTupleLog N p 0 < third ∧
        actualPrimeTupleLog N p 0 + actualPrimeTupleLog N p 1 +
          3 * actualPrimeTupleLog N p 2 < third := by
  simpa [prefix3, historicalPrefixProject, actualPrimeTupleLog] using
    P1ActualTuple.cube_tests_iff_log hN initial third (prefix3 p)
      (fun i => hpos ⟨i.val, by omega⟩)

/-- Exact membership for literal original-policy admitted fourth tuples
on a selected, whole-rough-active joint cell. -/
theorem mem_admitted_iff_log_on_selected_jointCell
    (e chi : ℝ) (m n : ℕ) (omega : ℝ) (N cap : ℕ) (hN : 1 < N)
    (hcap : (N : ℝ) ^ (19 / 96 : ℝ) ≤ (cap : ℝ))
    (p : Fin 4 → ℕ) (j3 : Cell m) (hj3 : j3 ∈ cells e chi m)
    (j4 : Fin 4 → Fin (n + 1))
    (hwhole : omega ≤ logPrimeMeshLo 0 (19 / 96) m j3 2)
    (ht : actualPrimeTupleLog N p ∈ jointCell m n j3 j4) :
    p ∈ firstExitAdmittedTuples 4 (policy e chi m omega (N : ℝ))
        (roughPrimeUniverse N cap 0 ((N : ℝ) ^ (19 / 96 : ℝ))) ↔
      (∀ i, Nat.Prime (p i) ∧ ¬p i ∣ N ∧ 0 ≤ (p i : ℝ) ∧
        (p i : ℝ) < (N : ℝ) ^ (19 / 96 : ℝ)) ∧
      actualPrimeTupleLog N p ∈ jointRegion e omega m j3 := by
  have hfront := mem_actualPrimeAdmittedTuples_iff_of_cutoff_le_cap 4
    (policy e chi m omega (N : ℝ)) N cap 0 ((N : ℝ) ^ (19 / 96 : ℝ)) hcap p
  have hrough := rough_on_jointCell m n omega j3 j4 hwhole _ ht
  constructor
  · intro hp
    obtain ⟨hs, hprime, hvalid⟩ := hfront.mp hp
    have hpos : ∀ i, 0 < p i := fun i => (hprime i).1.pos
    have hv := (valid_fourth_iff e chi m omega (N : ℝ) p hpos hs).mp hvalid
    have hraw := rawLevel_on_selected_jointCell e chi m n omega N hN p hpos j3 hj3 j4 hwhole ht
    rw [hraw] at hv
    have hc := (cube_tests_iff_log hN (initial e) (levelExponent e (box m j3)) p hpos).mp
      ⟨hv.1, hv.2.2.1, hv.2.2.2⟩
    refine ⟨hprime, ?_⟩
    exact ⟨⟨(mem_gateRegion _ _ _).mpr
      ⟨(actualPrimeTupleLog_strictAnti_iff hN p hpos).mpr hs, hc⟩,
      (firstStop_iff_log e m N p).mp hv.2.1⟩, hrough⟩
  · rintro ⟨hprime, ⟨hgate, hstop⟩, _hrough⟩
    have hpos : ∀ i, 0 < p i := fun i => (hprime i).1.pos
    have hg := (mem_gateRegion _ _ _).mp hgate
    have hs := (actualPrimeTupleLog_strictAnti_iff hN p hpos).mp hg.1
    have hc := (cube_tests_iff_log hN (initial e) (levelExponent e (box m j3)) p hpos).mpr hg.2
    have hraw := rawLevel_on_selected_jointCell e chi m n omega N hN p hpos j3 hj3 j4 hwhole ht
    apply hfront.mpr
    refine ⟨hs, hprime, (valid_fourth_iff e chi m omega (N : ℝ) p hpos hs).mpr ?_⟩
    rw [hraw]
    exact ⟨hc.1, (firstStop_iff_log e m N p).mpr hstop, hc.2.1, hc.2.2⟩

/-- Exact original-policy finite source equals its target-deleted fourth
prime box with the same cross-cell, first stop, three cubes and activation. -/
theorem admittedTuples_selected_jointCell_filter
    (e chi : ℝ) (m n : ℕ) (omega : ℝ) (N cap : ℕ) (hN : 1 < N)
    (hcap : (N : ℝ) ^ (19 / 96 : ℝ) ≤ (cap : ℝ))
    (j3 : Cell m) (hj3 : j3 ∈ cells e chi m) (j4 : Fin 4 → Fin (n + 1))
    (hwhole : omega ≤ logPrimeMeshLo 0 (19 / 96) m j3 2) :
    (firstExitAdmittedTuples 4 (policy e chi m omega (N : ℝ))
      (roughPrimeUniverse N cap 0 ((N : ℝ) ^ (19 / 96 : ℝ)))).filter
      (fun p => actualPrimeTupleLog N p ∈ jointCell m n j3 j4) =
    (actualPrimeBoxTuples N (fun _ : Fin 4 => (0 : ℝ)) (fun _ => (19 / 96 : ℝ))).filter
      (fun p => actualPrimeTupleLog N p ∈ jointCell m n j3 j4 ∩ jointRegion e omega m j3) := by
  ext p
  simp only [Finset.mem_filter, Set.mem_inter_iff]
  constructor
  · rintro ⟨hp, ht⟩
    have hd := (mem_admitted_iff_log_on_selected_jointCell e chi m n omega N cap hN hcap
      p j3 hj3 j4 hwhole ht).mp hp
    have hb : p ∈ actualPrimeBoxTuples N (fun _ : Fin 4 => (0 : ℝ)) (fun _ => (19 / 96 : ℝ)) :=
      (mem_actualPrimeBoxTuples_log_iff hN _ _ p).mpr
        ⟨fun i => ⟨(hd.1 i).1, (hd.1 i).2.1⟩,
          logPrimeMeshCell_subset_box (by norm_num : (0 : ℝ) < 19 / 96) n j4 ht.1⟩
    exact ⟨hb, ht, hd.2⟩
  · rintro ⟨hp, ht, hg⟩
    have hpi := mem_actualPrimeBoxTuples_iff.mp hp
    refine ⟨(mem_admitted_iff_log_on_selected_jointCell e chi m n omega N cap hN hcap
      p j3 hj3 j4 hwhole ht).mpr ⟨?_, hg⟩, ht⟩
    exact fun i => ⟨(hpi i).1, (hpi i).2.1, Nat.cast_nonneg _, (hpi i).2.2.2⟩

/-- On equal meshes the ancestor projection determines the unique joint
cell, so the additional cross intersection is exactly the fourth cell. -/
theorem jointCell_same_mesh (m : ℕ) (j4 : Fin 4 → Fin (m + 1)) :
    jointCell m m (prefix3 j4) j4 = logPrimeMeshCell 0 (19 / 96) m j4 := by
  ext t
  constructor
  · intro ht
    exact ht.1
  · intro ht
    exact ⟨ht, mem_logPrimeMeshCell_historicalPrefixProject (by omega : 3 ≤ 4) ht⟩

/-- Direct same-mesh interface for the original fourth lookup's selected
cell labels.  No newly supplied Q4 is needed for this parent dictionary. -/
theorem admittedTuples_selected_sameCell_filter
    (e chi : ℝ) (m : ℕ) (omega : ℝ) (N cap : ℕ) (hN : 1 < N)
    (hcap : (N : ℝ) ^ (19 / 96 : ℝ) ≤ (cap : ℝ))
    (j4 : Fin 4 → Fin (m + 1)) (hj3 : prefix3 j4 ∈ cells e chi m)
    (hwhole : omega ≤ logPrimeMeshLo 0 (19 / 96) m (prefix3 j4) 2) :
    (firstExitAdmittedTuples 4 (policy e chi m omega (N : ℝ))
      (roughPrimeUniverse N cap 0 ((N : ℝ) ^ (19 / 96 : ℝ)))).filter
      (fun p => actualPrimeTupleLog N p ∈ logPrimeMeshCell 0 (19 / 96) m j4) =
    (actualPrimeBoxTuples N (fun _ : Fin 4 => (0 : ℝ)) (fun _ => (19 / 96 : ℝ))).filter
      (fun p => actualPrimeTupleLog N p ∈ logPrimeMeshCell 0 (19 / 96) m j4 ∩
        jointRegion e omega m (prefix3 j4)) := by
  simpa only [jointCell_same_mesh] using
    admittedTuples_selected_jointCell_filter e chi m m omega N cap hN hcap
      (prefix3 j4) hj3 j4 hwhole

/-- The actual old residual reads this same selected third exponent at
its stored ancestor, including after a fourth prime has been selected. -/
theorem frozenLevel_on_selected_jointCell
    (e chi : ℝ) (m n : ℕ) (omega : ℝ) (N : ℕ) (hN : 1 < N)
    (p : Fin 4 → ℕ) (hpos : ∀ i, 0 < p i)
    (j3 : Cell m) (hj3 : j3 ∈ cells e chi m) (j4 : Fin 4 → Fin (n + 1))
    (hwhole : omega ≤ logPrimeMeshLo 0 (19 / 96) m j3 2)
    (ht : actualPrimeTupleLog N p ∈ jointCell m n j3 j4) :
    frozenLevel e chi m omega (N : ℝ) (history4 p) =
      (N : ℝ) ^ levelExponent e (box m j3) := by
  have hancestor : rosserAncestor 3 (history4 p) = history3 p := by
    simp [rosserAncestor, history4, history3, P1ActualTuple.history, prefix3, historicalPrefixProject]
  rw [frozenLevel, hancestor]
  exact rawLevel_on_selected_jointCell e chi m n omega N hN p hpos j3 hj3 j4 hwhole ht

/-- Conversion back from a genuine reverse history reads no default. -/
theorem history4_primeHistoryTuple (pre : List ℕ) (hlen : pre.length = 4) :
    history4 (primeHistoryTuple 4 pre) = pre := by
  simpa [history4, List.ofFn_succ] using primeHistoryTuple_reverse_ofFn hlen

/-- Original raw-Q3 constancy for arbitrary actual stored histories on a
selected joint cell, suitable as the inherited level of a new Q4 lookup. -/
theorem frozenLevel_history_on_selected_jointCell
    (e chi : ℝ) (m n : ℕ) (omega : ℝ) (N : ℕ) (hN : 1 < N)
    (pre : List ℕ) (hlen : pre.length = 4) (hpos : ∀ p ∈ pre, 0 < p)
    (j3 : Cell m) (hj3 : j3 ∈ cells e chi m) (j4 : Fin 4 → Fin (n + 1))
    (hwhole : omega ≤ logPrimeMeshLo 0 (19 / 96) m j3 2)
    (ht : primeHistoryLogCoordinates (N : ℝ) 4 pre ∈ jointCell m n j3 j4) :
    frozenLevel e chi m omega (N : ℝ) pre = (N : ℝ) ^ levelExponent e (box m j3) := by
  have htuplepos : ∀ i, 0 < primeHistoryTuple 4 pre i := primeHistoryTuple_pos hlen hpos
  have hcoords : actualPrimeTupleLog N (primeHistoryTuple 4 pre) =
      primeHistoryLogCoordinates (N : ℝ) 4 pre := by rfl
  have ht' : actualPrimeTupleLog N (primeHistoryTuple 4 pre) ∈ jointCell m n j3 j4 := by
    rw [hcoords]
    exact ht
  have h := frozenLevel_on_selected_jointCell e chi m n omega N hN
    (primeHistoryTuple 4 pre) htuplepos j3 hj3 j4 hwhole ht'
  rw [history4_primeHistoryTuple pre hlen] at h
  exact h

/-- Original half-open ownership determines the stopped first coarse label
uniquely; a point cannot borrow a different label's upper endpoint. -/
theorem firstStopRegion_on_cell (e : ℝ) (m : ℕ)
    (j4 : Fin 4 → Fin (m + 1)) (t : Fin 4 → ℝ)
    (ht : t ∈ logPrimeMeshCell 0 (19 / 96) m j4) :
    t ∈ firstStopRegion e m ↔
      logPrimeMeshHi 0 (19 / 96) m j4 0 ≤ VariableEnvelope.extendedFirstStop - 4 * e := by
  constructor
  · rintro ⟨i, hlo, hhi, hstop⟩
    have hown : (fun _ : Fin 1 => i) = (fun _ : Fin 1 => j4 0) := by
      apply logPrimeMeshCell_unique (by norm_num : (0 : ℝ) ≤ 19 / 96)
        (x := fun _ : Fin 1 => t 0)
      · apply mem_logPrimeMeshCell.mpr
        intro q
        fin_cases q
        exact ⟨hlo, hhi⟩
      · apply mem_logPrimeMeshCell.mpr
        intro q
        fin_cases q
        exact mem_logPrimeMeshCell.mp ht 0
    have hi : i = j4 0 := congrFun hown 0
    rw [hi] at hstop
    simpa only [logPrimeMeshHi] using hstop
  · intro hs
    have ht0 := mem_logPrimeMeshCell.mp ht 0
    exact ⟨j4 0, ht0.1, ht0.2, hs⟩

/-- This check records the original first-label stop; it is not a new
permission or a replacement of the initial policy. -/
def firstStopCellCheck (e : ℝ) (m : ℕ) (j4 : Fin 4 → Fin (m + 1)) : Bool :=
  decide (logPrimeMeshHi 0 (19 / 96) m j4 0 ≤ VariableEnvelope.extendedFirstStop - 4 * e)

theorem firstStopCellCheck_iff (e : ℝ) (m : ℕ) (j4 : Fin 4 → Fin (m + 1)) :
    firstStopCellCheck e m j4 = true ↔
      logPrimeMeshHi 0 (19 / 96) m j4 0 ≤ VariableEnvelope.extendedFirstStop - 4 * e := by
  simp only [firstStopCellCheck, decide_eq_true_eq]

/-- Additional lower truncation is explicit and independent of the original
mesh.  No positivity premise is needed for this exact region identity. -/
def truncatedJointRegion (e omega : ℝ) (m : ℕ) (j4 : Fin 4 → Fin (m + 1)) (a : ℝ) :
    Set (Fin 4 → ℝ) :=
  logPrimeBox (fun _ => a) (fun _ => (19 / 96 : ℝ)) ∩
    (logPrimeMeshCell 0 (19 / 96) m j4 ∩ jointRegion e omega m (prefix3 j4))

/-- A whole-active cell has exactly one first-stop branch.  The true branch
is one mixed box/mesh region with six strict nonzero affine rows; the false
branch is empty.  Neither first-stop nor rough activation is silently dropped. -/
theorem truncatedJointRegion_eq_if (e omega : ℝ) (m : ℕ)
    (j4 : Fin 4 → Fin (m + 1)) (a : ℝ)
    (hwhole : omega ≤ logPrimeMeshLo 0 (19 / 96) m (prefix3 j4) 2) :
    truncatedJointRegion e omega m j4 a =
      if firstStopCellCheck e m j4 = true then
        logPrimeBox (fun _ => a) (fun _ => (19 / 96 : ℝ)) ∩
          (logPrimeMeshCell 0 (19 / 96) m j4 ∩
            primeAffineGateRegion gateForms
              (gateBounds (initial e) (levelExponent e (box m (prefix3 j4)))))
      else ∅ := by
  by_cases hs : firstStopCellCheck e m j4 = true
  · rw [if_pos hs]
    ext t
    constructor
    · rintro ⟨hbox, ht, hregion⟩
      exact ⟨hbox, ht, hregion.1.1⟩
    · rintro ⟨hbox, ht, hgate⟩
      have hstop := (firstStopRegion_on_cell e m j4 t ht).mpr
        ((firstStopCellCheck_iff e m j4).mp hs)
      have ht3 := mem_logPrimeMeshCell_historicalPrefixProject (by omega : 3 ≤ 4) ht
      have hrough : omega ≤ t 2 := hwhole.trans (mem_logPrimeMeshCell.mp ht3 2).1
      exact ⟨hbox, ht, ⟨⟨hgate, hstop⟩, hrough⟩⟩
  · rw [if_neg hs]
    ext t
    constructor
    · rintro ⟨_hbox, ht, hregion⟩
      have hstop := (firstStopRegion_on_cell e m j4 t ht).mp hregion.1.2
      have hh := (firstStopCellCheck_iff e m j4).mpr hstop
      exact (hs hh).elim
    · intro ht
      exact ht.elim

/-- Actual lower-truncated source dictionary, valid for arbitrary a.  The
primes, target deletion, original first stop, three cubes and activation
are retained, now on the exact prime Ico carrier [N^a,N^(19/96)). -/
theorem truncated_admittedTuples_filter
    (e chi : ℝ) (m : ℕ) (omega : ℝ) (N cap : ℕ) (hN : 1 < N)
    (hcap : (N : ℝ) ^ (19 / 96 : ℝ) ≤ (cap : ℝ))
    (j4 : Fin 4 → Fin (m + 1)) (hj3 : prefix3 j4 ∈ cells e chi m)
    (hwhole : omega ≤ logPrimeMeshLo 0 (19 / 96) m (prefix3 j4) 2) (a : ℝ) :
    (firstExitAdmittedTuples 4 (policy e chi m omega (N : ℝ))
      (roughPrimeUniverse N cap 0 ((N : ℝ) ^ (19 / 96 : ℝ)))).filter
      (fun p => actualPrimeTupleLog N p ∈ logPrimeMeshCell 0 (19 / 96) m j4 ∧
        actualPrimeTupleLog N p ∈ logPrimeBox (fun _ => a) (fun _ => (19 / 96 : ℝ))) =
    (actualPrimeBoxTuples N (fun _ : Fin 4 => a) (fun _ => (19 / 96 : ℝ))).filter
      (fun p => actualPrimeTupleLog N p ∈ logPrimeMeshCell 0 (19 / 96) m j4 ∩
        jointRegion e omega m (prefix3 j4)) := by
  ext p
  simp only [Finset.mem_filter, Set.mem_inter_iff]
  constructor
  · rintro ⟨hp, ht, hbox⟩
    have htjoint : actualPrimeTupleLog N p ∈ jointCell m m (prefix3 j4) j4 := by
      rw [jointCell_same_mesh]
      exact ht
    have hd := (mem_admitted_iff_log_on_selected_jointCell e chi m m omega N cap hN hcap
      p (prefix3 j4) hj3 j4 hwhole htjoint).mp hp
    have hpbox := (mem_actualPrimeBoxTuples_log_iff hN _ _ p).mpr
      ⟨fun i => ⟨(hd.1 i).1, (hd.1 i).2.1⟩, hbox⟩
    exact ⟨hpbox, ht, hd.2⟩
  · rintro ⟨hpbox, ht, hg⟩
    have hpi := mem_actualPrimeBoxTuples_iff.mp hpbox
    have hbox := ((mem_actualPrimeBoxTuples_log_iff hN _ _ p).mp hpbox).2
    have htjoint : actualPrimeTupleLog N p ∈ jointCell m m (prefix3 j4) j4 := by
      rw [jointCell_same_mesh]
      exact ht
    refine ⟨(mem_admitted_iff_log_on_selected_jointCell e chi m m omega N cap hN hcap
      p (prefix3 j4) hj3 j4 hwhole htjoint).mpr ⟨?_, hg⟩, ht, hbox⟩
    exact fun i => ⟨(hpi i).1, (hpi i).2.1, Nat.cast_nonneg _, (hpi i).2.2.2⟩

/-- Direct mixed-gate source for prime Ico limits, including the original
first-stop false branch instead of assuming it away. -/
theorem truncated_admittedTuples_filter_eq_if
    (e chi : ℝ) (m : ℕ) (omega : ℝ) (N cap : ℕ) (hN : 1 < N)
    (hcap : (N : ℝ) ^ (19 / 96 : ℝ) ≤ (cap : ℝ))
    (j4 : Fin 4 → Fin (m + 1)) (hj3 : prefix3 j4 ∈ cells e chi m)
    (hwhole : omega ≤ logPrimeMeshLo 0 (19 / 96) m (prefix3 j4) 2) (a : ℝ) :
    (firstExitAdmittedTuples 4 (policy e chi m omega (N : ℝ))
      (roughPrimeUniverse N cap 0 ((N : ℝ) ^ (19 / 96 : ℝ)))).filter
      (fun p => actualPrimeTupleLog N p ∈ logPrimeMeshCell 0 (19 / 96) m j4 ∧
        actualPrimeTupleLog N p ∈ logPrimeBox (fun _ => a) (fun _ => (19 / 96 : ℝ))) =
    if firstStopCellCheck e m j4 = true then
      (actualPrimeBoxTuples N (fun _ : Fin 4 => a) (fun _ => (19 / 96 : ℝ))).filter
        (fun p => actualPrimeTupleLog N p ∈ logPrimeMeshCell 0 (19 / 96) m j4 ∩
          primeAffineGateRegion gateForms
            (gateBounds (initial e) (levelExponent e (box m (prefix3 j4)))))
    else ∅ := by
  rw [truncated_admittedTuples_filter e chi m omega N cap hN hcap j4 hj3 hwhole a]
  by_cases hs : firstStopCellCheck e m j4 = true
  · rw [if_pos hs]
    ext p
    simp only [Finset.mem_filter, Set.mem_inter_iff]
    constructor
    · rintro ⟨hp, ht, hg⟩
      exact ⟨hp, ht, hg.1.1⟩
    · rintro ⟨hp, ht, hg⟩
      have hstop := (firstStopRegion_on_cell e m j4 _ ht).mpr ((firstStopCellCheck_iff e m j4).mp hs)
      have ht3 := mem_logPrimeMeshCell_historicalPrefixProject (by omega : 3 ≤ 4) ht
      have hrough : omega ≤ actualPrimeTupleLog N p 2 :=
        hwhole.trans (mem_logPrimeMeshCell.mp ht3 2).1
      exact ⟨hp, ht, ⟨⟨hg, hstop⟩, hrough⟩⟩
  · rw [if_neg hs]
    apply Finset.eq_empty_iff_forall_not_mem.mpr
    intro p hp
    obtain ⟨_hpbox, ht, hg⟩ := Finset.mem_filter.mp hp
    have hstop := (firstStopRegion_on_cell e m j4 _ ht).mp hg.1.2
    exact hs ((firstStopCellCheck_iff e m j4).mpr hstop)

end HistoricalThirdCoarse.P1OriginalFourth
end
end ImbalancedChen
