import ImbalancedChen.P1OriginalVariableFourthBoundedSourceLimit

/-!
Whole original variable-fourth source: exact finite seed/activation labels.
SOURCE_WRITTEN / UNCOMPILED / NOT_ROOT_ACCEPTED / CODE_ONLY.

ALL fourth mesh labels are used, not selectedFourthCells or a supplied J4.
Every label is split at the exact inclusive rough third cutoff. Active and
selected third ancestors use their Gamma-2e; inactive and active-unselected
ancestors use the original Theta-2e fallback. The true admitted source keeps
firstStop, initial/current first cubes and current third cube.

This is an exact finite arithmetic/region dictionary. It asserts no global
mean, omitted-region estimate, small-prime tail, or cutoff-removal limit.
-/

namespace ImbalancedChen.P1OriginalVariableFourthFullSourceActivation
noncomputable section
open Filter Topology MeasureTheory Set
open scoped Classical BigOperators
open HistoricalThirdCoarse VariableEnvelope
open P2OriginalFourthCapProducerInterface
open P1OriginalCoarseContinuation P1OriginalCoarseFourthResidual
open P1OriginalVariableFourthContinuation
open HistoricalThirdCoarse.P1OriginalFourth

abbrev Label (m : ℕ) := FourthCell m × Bool

/-- Equality at the rough cutoff belongs to the active branch. -/
def activationRegion (omega : ℝ) (on : Bool) : Set Point :=
  {t | if on then omega ≤ t 2 else t 2 < omega}

def meshBranch (m : ℕ) (omega : ℝ) (label : Label m) : Set Point :=
  logPrimeMeshCell 0 (19 / 96) m label.1 ∩ activationRegion omega label.2

/-- The branch seed is Gamma only for an active adopted THIRD ancestor.
All other labels preserve the initial Theta fallback. -/
def branchSeed (e chi : ℝ) (m : ℕ) (label : Label m) : ℝ :=
  if label.2 = true ∧ prefix3 label.1 ∈ cells e chi m then
    levelExponent e (box m (prefix3 label.1)) else initial e

def coordinateSeed (e chi : ℝ) (m : ℕ) (omega : ℝ) (t : Point) : ℝ :=
  if omega ≤ t 2 then exponent e chi m (prefix3 t) else initial e

/-- The full actual admitted region on one finite seed branch. -/
def sourceBranch (e chi : ℝ) (m : ℕ) (omega : ℝ) (label : Label m) : Set Point :=
  meshBranch m omega label ∩
    (primeAffineGateRegion gateForms (gateBounds (initial e) (branchSeed e chi m label)) ∩
      firstStopRegion e m)

theorem ancestor3_tupleHistory (p : Fin 4 → ℕ) :
    rosserAncestor 3 (tupleHistory p) = history3 p := by
  simp [tupleHistory, List.ofFn_succ, rosserAncestor, history3,
    HistoricalThirdCoarse.P1ActualTuple.history, prefix3, historicalPrefixProject]

theorem history3_coordinates (N : ℕ) (p : Fin 4 → ℕ) :
    primeHistoryLogCoordinates (N : ℝ) 3 (history3 p) = prefix3 (actualPrimeTupleLog N p) := by
  rw [history3_log, prefix3_log]

theorem active_history3_iff (N : ℕ) (hN : 1 < N) (omega : ℝ) (p : Fin 4 → ℕ)
    (hp : ∀ i, 0 < p i) :
    active omega (N : ℝ) (history3 p) ↔ omega ≤ actualPrimeTupleLog N p 2 := by
  simpa only [history3, prefix3, historicalPrefixProject, actualPrimeTupleLog] using
    HistoricalThirdCoarse.P1ActualTuple.active_iff_log hN omega (prefix3 p)
      (fun i => hp ⟨i.val, by omega⟩)

/-- The original rawQ3 seed has a coordinate formula on EVERY fourth
prime tuple, including active-but-unselected ancestors. -/
theorem seedExponent_eq_coordinateSeed (e chi : ℝ) (m : ℕ) (omega : ℝ)
    (N : ℕ) (hN : 1 < N) (p : Fin 4 → ℕ) (hp : ∀ i, 0 < p i) :
    seedExponent e chi m omega (N : ℝ) (tupleHistory p) =
      coordinateSeed e chi m omega (actualPrimeTupleLog N p) := by
  have hactive := active_history3_iff N hN omega p hp
  have hcoords := history3_coordinates N p
  unfold seedExponent
  rw [ancestor3_tupleHistory]
  unfold P1CoarseFirstCubeFallbackMargin.effectiveExponent coordinateSeed
  by_cases ha : omega ≤ actualPrimeTupleLog N p 2
  · by_cases hc : ∃ j ∈ cells e chi m,
        prefix3 (actualPrimeTupleLog N p) ∈ logPrimeMeshCell 0 (19 / 96) m j
    · have hs : P1ThirdFallbackSupport.supported e chi m omega (N : ℝ) (history3 p) := by
        refine ⟨hactive.mpr ha, ?_⟩
        rwa [hcoords]
      rw [if_pos hs, if_pos ha, hcoords]
    · have hs : ¬ P1ThirdFallbackSupport.supported e chi m omega (N : ℝ) (history3 p) := by
        intro hs
        apply hc
        simpa only [P1ThirdFallbackSupport.jointCells, hcoords, mem_setOf_eq] using hs.2
      rw [if_neg hs, if_pos ha]
      symm
      exact exponent_outside e chi m _ (fun j hj ht => hc ⟨j, hj, ht⟩)
  · have hs : ¬ P1ThirdFallbackSupport.supported e chi m omega (N : ℝ) (history3 p) :=
      fun hs => ha (hactive.mp hs.1)
    rw [if_neg hs, if_neg ha]

/-- Exact finite branch identification. No selected fourth-label premise
is present: the third ancestor may be inactive OR unselected. -/
theorem coordinateSeed_on_meshBranch (e chi : ℝ) (m : ℕ) (omega : ℝ)
    (label : Label m) {t : Point} (ht : t ∈ meshBranch m omega label) :
    coordinateSeed e chi m omega t = branchSeed e chi m label := by
  have ht3 : prefix3 t ∈ logPrimeMeshCell 0 (19 / 96) m (prefix3 label.1) :=
    mem_logPrimeMeshCell_historicalPrefixProject (by omega : 3 ≤ 4) ht.1
  have ha := ht.2
  cases hflag : label.2
  · simp only [activationRegion, mem_setOf_eq, hflag, Bool.false_eq_true, if_false] at ha
    simp only [coordinateSeed, if_neg (not_le.mpr ha), branchSeed, hflag,
      Bool.false_eq_true, false_and, if_false]
  · simp only [activationRegion, mem_setOf_eq, hflag, if_true] at ha
    rw [coordinateSeed, if_pos ha]
    by_cases hj : prefix3 label.1 ∈ cells e chi m
    · simpa [branchSeed, hflag, hj] using exponent_on_cell e chi m _ _ hj ht3
    · have hvalue : exponent e chi m (prefix3 t) = initial e := by
        apply exponent_outside
        intro k hk htk
        have heq : k = prefix3 label.1 :=
          logPrimeMeshCell_unique (by norm_num : (0 : ℝ) ≤ 19 / 96) htk ht3
        exact hj (heq ▸ hk)
      simpa [branchSeed, hflag, hj] using hvalue

theorem seedExponent_on_meshBranch (e chi : ℝ) (m : ℕ) (omega : ℝ)
    (label : Label m) (N : ℕ) (hN : 1 < N) (p : Fin 4 → ℕ) (hp : ∀ i, 0 < p i)
    (ht : actualPrimeTupleLog N p ∈ meshBranch m omega label) :
    seedExponent e chi m omega (N : ℝ) (tupleHistory p) = branchSeed e chi m label := by
  rw [seedExponent_eq_coordinateSeed e chi m omega N hN p hp]
  exact coordinateSeed_on_meshBranch e chi m omega label ht

/-- The inactive branch keeps Theta even over an adopted third cell. -/
theorem branchSeed_inactive (e chi : ℝ) (m : ℕ) (j : FourthCell m) :
    branchSeed e chi m (j, false) = initial e := by simp [branchSeed]

/-- Active, unselected ancestors also keep Theta; rough activation alone
never licenses a Gamma replacement. -/
theorem branchSeed_active_unselected (e chi : ℝ) (m : ℕ) (j : FourthCell m)
    (hj : prefix3 j ∉ cells e chi m) : branchSeed e chi m (j, true) = initial e := by
  simp [branchSeed, hj]

theorem branchSeed_active_selected (e chi : ℝ) (m : ℕ) (j : FourthCell m)
    (hj : prefix3 j ∈ cells e chi m) :
    branchSeed e chi m (j, true) = levelExponent e (box m (prefix3 j)) := by
  simp [branchSeed, hj]

/-- Every positive-cube point has exactly one mesh/rough activation label. -/
theorem exists_meshBranch (m : ℕ) (omega : ℝ) {t : Point}
    (ht : t ∈ logPrimeBox (fun _ : Fin 4 => (0 : ℝ)) (fun _ => (19 / 96 : ℝ))) :
    ∃ label : Label m, t ∈ meshBranch m omega label := by
  obtain ⟨j, hj⟩ := exists_logPrimeMeshCell 0 (19 / 96) m ht
  by_cases ha : omega ≤ t 2
  · exact ⟨(j, true), hj, by simpa [activationRegion] using ha⟩
  · exact ⟨(j, false), hj, by simpa [activationRegion] using lt_of_not_ge ha⟩

theorem meshBranch_unique (m : ℕ) (omega : ℝ) {l r : Label m} {t : Point}
    (hl : t ∈ meshBranch m omega l) (hr : t ∈ meshBranch m omega r) : l = r := by
  have hj : l.1 = r.1 := logPrimeMeshCell_unique (by norm_num : (0 : ℝ) ≤ 19 / 96) hl.1 hr.1
  have hb : l.2 = r.2 := by
    have hal := hl.2
    have har := hr.2
    cases hleft : l.2 <;> cases hright : r.2 <;>
      simp only [activationRegion, mem_setOf_eq, hleft, hright, Bool.false_eq_true,
        if_false, if_true] at hal har ⊢ <;> try rfl <;> linarith
  exact Prod.ext hj hb

theorem measurableSet_meshBranch (m : ℕ) (omega : ℝ) (label : Label m) :
    MeasurableSet (meshBranch m omega label) := by
  apply (measurableSet_logPrimeBox _ _).inter
  cases h : label.2
  · simpa only [activationRegion, h, Bool.false_eq_true, if_false] using
      (isOpen_lt (continuous_apply (2 : Fin 4)) continuous_const).measurableSet
  · simpa only [activationRegion, h, if_true] using
      (isClosed_le continuous_const (continuous_apply (2 : Fin 4))).measurableSet

theorem measurableSet_sourceBranch (e chi : ℝ) (m : ℕ) (omega : ℝ) (label : Label m) :
    MeasurableSet (sourceBranch e chi m omega label) :=
  (measurableSet_meshBranch m omega label).inter
    ((measurableSet_primeAffineGateRegion _ _).inter (firstStopRegion_measurable e m))

/-- Each full-source label is an exact mixed-affine region (or empty), with
all six original strict order/cube rows and an inclusive/strict rough row.
No whole-rough-active box is required. -/
theorem sourceBranch_eq_firstStop_if (e chi : ℝ) (m : ℕ) (omega : ℝ) (label : Label m) :
    sourceBranch e chi m omega label =
      if firstStopCellCheck e m label.1 = true then
        meshBranch m omega label ∩
          primeAffineGateRegion gateForms (gateBounds (initial e) (branchSeed e chi m label))
      else ∅ := by
  by_cases hs : firstStopCellCheck e m label.1 = true
  · rw [if_pos hs]
    ext t
    constructor
    · rintro ⟨hb, hg, _⟩
      exact ⟨hb, hg⟩
    · rintro ⟨hb, hg⟩
      exact ⟨hb, hg, (firstStopRegion_on_cell e m label.1 t hb.1).mpr
        ((firstStopCellCheck_iff e m label.1).mp hs)⟩
  · rw [if_neg hs]
    ext t
    constructor
    · rintro ⟨hb, _hg, hstop⟩
      exact hs ((firstStopCellCheck_iff e m label.1).mpr
        ((firstStopRegion_on_cell e m label.1 t hb.1).mp hstop))
    · intro ht
      exact False.elim ht

/-- Reuse the actual third-tuple power/log dictionary for all fourth seeds. -/
theorem cube_tests_iff_log (N : ℕ) (hN : 1 < N) (p : Fin 4 → ℕ) (hp : ∀ i, 0 < p i)
    (old seed : ℝ) :
    ((p 0 : ℝ) ^ 3 < (N : ℝ) ^ old ∧ (p 0 : ℝ) ^ 3 < (N : ℝ) ^ seed ∧
      (p 0 : ℝ) * p 1 * (p 2 : ℝ) ^ 3 < (N : ℝ) ^ seed) ↔
      3 * actualPrimeTupleLog N p 0 < old ∧ 3 * actualPrimeTupleLog N p 0 < seed ∧
        actualPrimeTupleLog N p 0 + actualPrimeTupleLog N p 1 + 3 * actualPrimeTupleLog N p 2 < seed := by
  simpa [prefix3, historicalPrefixProject, actualPrimeTupleLog] using
    HistoricalThirdCoarse.P1ActualTuple.cube_tests_iff_log hN old seed (prefix3 p)
      (fun i => hp ⟨i.val, by omega⟩)

/-- Exact original admission on every branch of the FULL positive box.
The current first cube and third cube survive in the initial fallback
branches too; firstStop is never erased. -/
theorem mem_admitted_on_meshBranch_iff
    (e chi : ℝ) (m : ℕ) (omega a : ℝ) (N cap : ℕ) (hN : 1 < N)
    (hcap : (N : ℝ) ^ (19 / 96 : ℝ) ≤ (cap : ℝ))
    (p : Fin 4 → ℕ)
    (hpbox : p ∈ actualPrimeBoxTuples N (fun _ : Fin 4 => a) (fun _ => (19 / 96 : ℝ)))
    (label : Label m) (ht : actualPrimeTupleLog N p ∈ meshBranch m omega label) :
    p ∈ firstExitAdmittedTuples 4 (HistoricalThirdCoarse.policy e chi m omega (N : ℝ))
        (roughPrimeUniverse N cap 0 ((N : ℝ) ^ (19 / 96 : ℝ))) ↔
      actualPrimeTupleLog N p ∈ sourceBranch e chi m omega label := by
  have hpi := mem_actualPrimeBoxTuples_iff.mp hpbox
  have hpos : ∀ i, 0 < p i := fun i => (hpi i).1.pos
  have hraw : rawLevel e chi m omega (N : ℝ) (history3 p) =
      (N : ℝ) ^ branchSeed e chi m label := by
    have hh := P1OriginalVariableFourthContinuation.frozenLevel_eq_rpow_seed e chi m omega (N : ℝ) (tupleHistory p)
    change rawLevel e chi m omega (N : ℝ) (rosserAncestor 3 (tupleHistory p)) = _ at hh
    rw [ancestor3_tupleHistory, seedExponent_on_meshBranch e chi m omega label N hN p hpos ht] at hh
    exact hh
  have hfront := mem_actualPrimeAdmittedTuples_iff_of_cutoff_le_cap 4
    (HistoricalThirdCoarse.policy e chi m omega (N : ℝ)) N cap 0 ((N : ℝ) ^ (19 / 96 : ℝ)) hcap p
  constructor
  · intro hp
    obtain ⟨hs, _hprime, hv⟩ := hfront.mp hp
    have hv' := (valid_fourth_iff e chi m omega (N : ℝ) p hpos hs).mp hv
    rw [hraw] at hv'
    have hc := (cube_tests_iff_log N hN p hpos (initial e) (branchSeed e chi m label)).mp
      ⟨hv'.1, hv'.2.2.1, hv'.2.2.2⟩
    exact ⟨ht, (mem_gateRegion _ _ _).mpr
      ⟨(actualPrimeTupleLog_strictAnti_iff hN p hpos).mpr hs, hc⟩,
      (firstStop_iff_log e m N p).mp hv'.2.1⟩
  · rintro ⟨_ht, hg, hstop⟩
    have hg' := (mem_gateRegion _ _ _).mp hg
    have hs := (actualPrimeTupleLog_strictAnti_iff hN p hpos).mp hg'.1
    have hc := (cube_tests_iff_log N hN p hpos (initial e) (branchSeed e chi m label)).mpr hg'.2
    apply hfront.mpr
    refine ⟨hs, fun i => ⟨(hpi i).1, (hpi i).2.1, Nat.cast_nonneg _, (hpi i).2.2.2⟩, ?_⟩
    apply (valid_fourth_iff e chi m omega (N : ℝ) p hpos hs).mpr
    rw [hraw]
    exact ⟨hc.1, (firstStop_iff_log e m N p).mpr hstop, hc.2⟩

/-- Whole admitted source inside the positive prime box equals the union
of ALL finite branch labels. No fourth selected-cell support is assumed. -/
theorem mem_admitted_iff_exists_sourceBranch
    (e chi : ℝ) (m : ℕ) (omega a : ℝ) (ha : 0 ≤ a) (N cap : ℕ) (hN : 1 < N)
    (hcap : (N : ℝ) ^ (19 / 96 : ℝ) ≤ (cap : ℝ)) (p : Fin 4 → ℕ)
    (hpbox : p ∈ actualPrimeBoxTuples N (fun _ : Fin 4 => a) (fun _ => (19 / 96 : ℝ))) :
    p ∈ firstExitAdmittedTuples 4 (HistoricalThirdCoarse.policy e chi m omega (N : ℝ))
        (roughPrimeUniverse N cap 0 ((N : ℝ) ^ (19 / 96 : ℝ))) ↔
      ∃ label : Label m, actualPrimeTupleLog N p ∈ sourceBranch e chi m omega label := by
  have hx := ((mem_actualPrimeBoxTuples_log_iff hN _ _ p).mp hpbox).2
  have hx0 : actualPrimeTupleLog N p ∈ logPrimeBox (fun _ : Fin 4 => (0 : ℝ)) (fun _ => (19 / 96 : ℝ)) :=
    mem_logPrimeBox.mpr (fun i => ⟨ha.trans (mem_logPrimeBox.mp hx i).1, (mem_logPrimeBox.mp hx i).2⟩)
  obtain ⟨label, ht⟩ := exists_meshBranch m omega hx0
  constructor
  · intro hp
    exact ⟨label, (mem_admitted_on_meshBranch_iff e chi m omega a N cap hN hcap p hpbox label ht).mp hp⟩
  · rintro ⟨other, hother⟩
    exact (mem_admitted_on_meshBranch_iff e chi m omega a N cap hN hcap p hpbox other hother.1).mpr hother

/-- Exact branch residual dictionary for every original mesh/activation
branch, including both Theta fallback branches. All producer rows remain
in the pointwise maximum seeded by that branch's true old rawQ3 exponent. -/
theorem literalResidual_eq_branch_profile
    (e chi : ℝ) (m : ℕ) (omega : ℝ) (label : Label m)
    (N cap : ℕ) (hN : 1 < N) (p : Fin 4 → ℕ) (hp : ∀ i, 0 < p i)
    (ht : actualPrimeTupleLog N p ∈ meshBranch m omega label)
    (rows : Finset ProducerRow) (licensed : ProducerRow → Prop) :
    literalTupleResidualDifference (rawLevel e chi m omega (N : ℝ))
        (producerLevel4 e chi m omega (N : ℝ) rows licensed) N cap p =
      fourthTuplePlusResidualP1 N cap (branchSeed e chi m label) p -
        fourthTuplePlusResidualP1 N cap
          (producerProfile4 e rows licensed (branchSeed e chi m label) (actualPrimeTupleLog N p)) p := by
  have hs := seedExponent_on_meshBranch e chi m omega label N hN p hp ht
  have hold := P1OriginalVariableFourthContinuation.frozenLevel_eq_rpow_seed
    e chi m omega (N : ℝ) (tupleHistory p)
  change rawLevel e chi m omega (N : ℝ) (rosserAncestor 3 (tupleHistory p)) = _ at hold
  rw [hs] at hold
  have hnew : producerLevel4 e chi m omega (N : ℝ) rows licensed (tupleHistory p) =
      (N : ℝ) ^ producerProfile4 e rows licensed (branchSeed e chi m label) (actualPrimeTupleLog N p) := by
    simp only [producerLevel4, level4, exponent4, show (tupleHistory p).length = 4 by simp [tupleHistory],
      if_pos, hs, tupleHistory_log, producerProfile4]
  unfold literalTupleResidualDifference fourthTuplePlusResidualP1
  rw [hold, hnew]
  ring

/-- Finite full-frontier to labelled-region sum identity on the whole
positive prime box. The label family is all fourth mesh cells times Bool. -/
theorem admitted_box_sum_eq_all_branch_sums
    (e chi : ℝ) (m : ℕ) (omega a : ℝ) (ha : 0 ≤ a) (N cap : ℕ) (hN : 1 < N)
    (hcap : (N : ℝ) ^ (19 / 96 : ℝ) ≤ (cap : ℝ)) (f : (Fin 4 → ℕ) → ℝ) :
    (∑ p ∈ actualPrimeBoxTuples N (fun _ : Fin 4 => a) (fun _ => (19 / 96 : ℝ)),
      (∏ i, 1 / ((p i : ℝ) - 1)) *
        (if p ∈ firstExitAdmittedTuples 4 (HistoricalThirdCoarse.policy e chi m omega (N : ℝ))
          (roughPrimeUniverse N cap 0 ((N : ℝ) ^ (19 / 96 : ℝ))) then f p else 0)) =
    ∑ label : Label m,
      ∑ p ∈ actualPrimeBoxTuples N (fun _ : Fin 4 => a) (fun _ => (19 / 96 : ℝ)),
        (∏ i, 1 / ((p i : ℝ) - 1)) *
          (if actualPrimeTupleLog N p ∈ sourceBranch e chi m omega label then f p else 0) := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p hp
  have hiff := mem_admitted_iff_exists_sourceBranch e chi m omega a ha N cap hN hcap p hp
  by_cases hs : ∃ label : Label m, actualPrimeTupleLog N p ∈ sourceBranch e chi m omega label
  · obtain ⟨label, ht⟩ := hs
    rw [if_pos (hiff.mpr ⟨label, ht⟩), Finset.sum_eq_single label]
    · rw [if_pos ht]
    · intro other _ho hne
      rw [if_neg (show actualPrimeTupleLog N p ∉ sourceBranch e chi m omega other from by
        intro hother
        exact hne (meshBranch_unique m omega hother.1 ht.1)), mul_zero]
    · simp
  · rw [if_neg (mt hiff.mp hs)]
    symm
    apply Finset.sum_eq_zero
    intro label _hl
    rw [if_neg (fun ht => hs ⟨label, ht⟩), mul_zero]

/-- The actual whole positive-box variable-fourth correction has a finite
all-branch arithmetic dictionary. This includes the omitted active-unselected
and inactive branches with their original initial seed and firstStop gates. -/
theorem full_variable_correction_eq_all_branch_residuals
    (e chi : ℝ) (m : ℕ) (omega a : ℝ) (ha : 0 ≤ a) (N cap : ℕ) (hN : 1 < N)
    (hcap : (N : ℝ) ^ (19 / 96 : ℝ) ≤ (cap : ℝ))
    (rows : Finset ProducerRow) (licensed : ProducerRow → Prop) :
    (∑ p ∈ actualPrimeBoxTuples N (fun _ : Fin 4 => a) (fun _ => (19 / 96 : ℝ)),
      (∏ i, 1 / ((p i : ℝ) - 1)) *
        (if p ∈ firstExitAdmittedTuples 4 (HistoricalThirdCoarse.policy e chi m omega (N : ℝ))
          (roughPrimeUniverse N cap 0 ((N : ℝ) ^ (19 / 96 : ℝ))) then
          literalTupleResidualDifference (rawLevel e chi m omega (N : ℝ))
            (producerLevel4 e chi m omega (N : ℝ) rows licensed) N cap p else 0)) =
    ∑ label : Label m,
      ∑ p ∈ actualPrimeBoxTuples N (fun _ : Fin 4 => a) (fun _ => (19 / 96 : ℝ)),
        (∏ i, 1 / ((p i : ℝ) - 1)) *
          (if actualPrimeTupleLog N p ∈ sourceBranch e chi m omega label then
            fourthTuplePlusResidualP1 N cap (branchSeed e chi m label) p -
              fourthTuplePlusResidualP1 N cap
                (producerProfile4 e rows licensed (branchSeed e chi m label) (actualPrimeTupleLog N p)) p
           else 0) := by
  rw [admitted_box_sum_eq_all_branch_sums e chi m omega a ha N cap hN hcap]
  apply Finset.sum_congr rfl
  intro label _hl
  apply Finset.sum_congr rfl
  intro p hp
  by_cases hs : actualPrimeTupleLog N p ∈ sourceBranch e chi m omega label
  · simp only [if_pos hs]
    rw [literalResidual_eq_branch_profile e chi m omega label N cap hN p
      (fun i => (mem_actualPrimeBoxTuples_iff.mp hp i).1.pos) hs.1 rows licensed]
  · simp only [if_neg hs]

end
end ImbalancedChen.P1OriginalVariableFourthFullSourceActivation


