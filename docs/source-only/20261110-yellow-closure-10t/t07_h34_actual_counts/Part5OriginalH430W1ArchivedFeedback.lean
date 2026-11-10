import ImbalancedChen.Part5OriginalH430CorrectedWinningSource
import ImbalancedChen.Certificates.RationalLogCertificate

/-! Original W1 archive weights against their actual singleton integrals.
The sparse list stores a lower bound on one half of two log ratios for
each preimage of a lower-table cell. Closed finite arithmetic proof bodies
below are unevaluated. Source formulas are generator-0025.py, lines 43–51,
and generator-0590.py, lines 158–176, in the P5 manuscript supplement. -/

namespace ImbalancedChen.Part5OriginalH430W1ArchivedFeedback

noncomputable section
open Set MeasureTheory
open scoped BigOperators
open Certificates (logSeriesLower logSeriesUpper RationalLogCertificate)
open P2Selected430CausalOccurrenceExporter (Table iterate read)
open P2Selected430LiteralActionData (rows)
open P5OriginalActionMassBound P5OriginalFeedbackDomains P5OriginalFeedbackTableKernels
open Part5OriginalUpsilon5CausalDictionary
open Part5OriginalH430ArithmeticAtomRows Part5OriginalH430LiteralBankBudget
open Part5OriginalH430FixedReadRows Part5OriginalH430BankSlotTargets
open Part5OriginalH430ActualFeedbackQuotientRemainders
open Part5OriginalH430DecisionProvenance (iterate_nonneg)
open Part5OriginalH430ImmutableBankProfiles (precedingH precedingh)
open Part5OriginalH430PhysicalRoots Part5OriginalH430RequestedHistory
open Part5OriginalH430RequestedLevelBankSupply
open Part5OriginalH430SelectedBankGlobalFloorBaseLedger
open Part5OriginalH430ActualReadEdgeDefect Part5OriginalH430SelectedFixedReadSupply
open Part5OriginalH430FixedReadDictionary

private def gridQ (k : ℕ) : ℚ := 1 + (k : ℚ) / 50
private def targetQ (i : Fin 7) : ℚ := 12/5 + (i.val : ℚ)/10
private def anchorQ (j : Fin 10) : ℚ := 16/5 + (j.val : ℚ)/5

private def left (j : Fin 10) (k : ℕ) : ℚ :=
  max (1/anchorQ j) (1 - gridQ (k+1)/anchorQ j)

private def right (i : Fin 7) (j : Fin 10) (k : ℕ) : ℚ :=
  min (1/targetQ i) (1 - gridQ k/anchorQ j)

private def weightAt (xs : List (ℕ × ℤ)) (k : ℕ) : ℤ :=
  (xs.map (fun w => if w.1 = k then w.2 else 0)).sum

/-- The whole archived coefficient of the cell, including every occurrence
of its index if present. -/
def archiveWeight (i : Fin 7) (j : Fin 10) (k : ℕ) : ℤ :=
  weightAt (rows (slotOfAction (.inl (i,j)))).lowerWeights k

private def logLower (l r : ℚ) : ℚ :=
  (logSeriesLower (r/l) 32 + logSeriesLower ((1-l)/(1-r)) 32) / 2

private def guardCell (i : Fin 7) (j : Fin 10) (k : ℕ) : Bool :=
  let w := archiveWeight i j k
  let l := left j k
  let r := right i j k
  decide (w = 0 ∨
    (0 < w ∧ 2 ≤ gridQ k ∧ gridQ (k+1) ≤ 5 ∧
      0 < l ∧ l < r ∧ r < 1 ∧ (w : ℚ)/(2^80 : ℚ) ≤ logLower l r))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- Each closed arithmetic check refers to the original slot. It makes no
test of a real integral, prime count, asymptotic formula or final bound. -/
private theorem row_checks (i : Fin 7) (j : Fin 10) :
    (List.range 200).all (guardCell i j) = true ∧
      (rows (slotOfAction (.inl (i,j)))).upperWeights = [] ∧
      (rows (slotOfAction (.inl (i,j)))).divisor = 1 := by
  fin_cases i <;> fin_cases j <;> decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- Exhaustive original sparse-list coverage for every W1 slot. -/
theorem original_w1_indices (i : Fin 7) (j : Fin 10) :
    let xs := (rows (slotOfAction (.inl (i,j)))).lowerWeights
    (xs.map Prod.fst).Nodup ∧ xs.all (fun w => decide (w.1 < 200 ∧ 0 < w.2)) = true := by
  fin_cases i <;> fin_cases j <;> decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem original_w1_feedback_count :
    (∑ i : Fin 7, ∑ j : Fin 10, (rows (slotOfAction (.inl (i,j)))).lowerWeights.length) =
      1858 := by decide

private theorem series_lower {x : ℚ} (hx : 1 ≤ x) :
    (logSeriesLower x 32 : ℝ) ≤ Real.log (x : ℝ) := by
  let c : RationalLogCertificate := ⟨x, 32, logSeriesLower x 32, logSeriesUpper x 32⟩
  have hc : c.Valid := ⟨hx, le_rfl, le_rfl⟩
  have hh : c.check = true := decide_eq_true hc
  exact (c.check_sound hh).1

private theorem primitive {l r : ℝ} (hl : 0 < l) (hlr : l ≤ r) (hr : r < 1) :
    (∫ u in Ioo l r, 1 / (u * (1-u))) =
      Real.log (r/l) + Real.log ((1-l)/(1-r)) := by
  have hr0 := hl.trans_le hlr
  have h1l : 0 < 1-l := by linarith
  have h1r : 0 < 1-r := by linarith
  let F := fun u : ℝ => Real.log u - Real.log (1-u)
  have hc : ContinuousOn (fun u : ℝ => 1/(u*(1-u))) (Icc l r) := by
    apply continuousOn_const.div
    · fun_prop
    · intro u hu
      exact (mul_pos (hl.trans_le hu.1) (by linarith [hu.2] : 0 < 1-u)).ne'
  have hd : ∀ u ∈ uIcc l r, HasDerivAt F (1/(u*(1-u))) u := by
    intro u hu
    rw [uIcc_of_le hlr] at hu
    have hu0 := hl.trans_le hu.1
    have hu1 : 0 < 1-u := by linarith [hu.2]
    have hlog := ((hasDerivAt_const u (1 : ℝ)).sub (hasDerivAt_id u)).log hu1.ne'
    apply ((Real.hasDerivAt_log hu0.ne').sub hlog).congr_deriv
    field_simp [hu0.ne', hu1.ne'] <;> ring
  rw [integral_Ioo_eq_integral_Ioc, ← intervalIntegral.integral_of_le hlr,
    intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hc.intervalIntegrable_of_Icc hlr)]
  rw [Real.log_div hr0.ne' hl.ne', Real.log_div h1l.ne' h1r.ne']
  dsimp [F]
  ring

private theorem original_preimage (i : Fin 7) (j : Fin 10) (k : Fin 200)
    (h2 : 2 ≤ gridQ k.val) (h5 : gridQ (k.val+1) ≤ 5) :
    Ioo (1/W1Anchor j) (1/W1Target i) ∩
      tablePullback true (singletonProfile (W1Anchor j)) (.inl k) =
        Ioo (left j k.val : ℝ) (right i j k.val : ℝ) := by
  have ha : 0 < W1Anchor j := by unfold W1Anchor; positivity
  have hgrid (q : ℕ) : (gridQ q : ℝ) = floorGrid q := by simp [gridQ, floorGrid]
  have h2' : (2 : ℝ) ≤ floorGrid k.val := by rw [← hgrid]; exact_mod_cast h2
  have h5' : floorGrid (k.val+1) ≤ (5 : ℝ) := by rw [← hgrid]; exact_mod_cast h5
  have hleft : (left j k.val : ℝ) =
      max (1/W1Anchor j) (1-floorGrid (k.val+1)/W1Anchor j) := by
    simp [left, anchorQ, gridQ, W1Anchor, floorGrid]
  have hright : (right i j k.val : ℝ) =
      min (1/W1Target i) (1-floorGrid k.val/W1Anchor j) := by
    simp [right, targetQ, anchorQ, gridQ, W1Target, W1Anchor, floorGrid]
  rw [hleft, hright]
  ext u
  have hi (x : ℝ) : 1-x/W1Anchor j < u ↔ W1Anchor j*(1-u) < x := by
    calc
      _ ↔ 1-u < x/W1Anchor j := by constructor <;> intro h <;> linarith only [h]
      _ ↔ _ := by rw [lt_div_iff₀ ha, mul_comm]
  have lo (x : ℝ) : u < 1-x/W1Anchor j ↔ x < W1Anchor j*(1-u) := by
    calc
      _ ↔ x/W1Anchor j < 1-u := by constructor <;> intro h <;> linarith only [h]
      _ ↔ _ := by rw [div_lt_iff₀ ha, mul_comm]
  change ((1/W1Anchor j < u ∧ u < 1/W1Target i) ∧
    (2 ≤ W1Anchor j*(1-u) ∧ W1Anchor j*(1-u) ≤ 5) ∧
    floorGrid k.val < W1Anchor j*(1-u) ∧ W1Anchor j*(1-u) < floorGrid (k.val+1)) ↔
    (max _ _ < u ∧ u < min _ _)
  rw [max_lt_iff, lt_min_iff, hi, lo]
  constructor
  · rintro ⟨⟨hl,hr⟩,_,hc,hb⟩
    exact ⟨⟨hl,hb⟩,hr,hc⟩
  · rintro ⟨⟨hl,hb⟩,hr,hc⟩
    exact ⟨⟨hl,hr⟩,⟨h2'.trans hc.le, hb.le.trans h5'⟩,hc,hb⟩

/-- The entire lower weight in each actual W1 slot/cell is at most its
true normalized singleton coefficient, with exactly one half. -/
theorem archive_weight_le_dynamic_ideal (i : Fin 7) (j : Fin 10) (k : Fin 200) :
    (archiveWeight i j k.val : ℝ)/(2^80 : ℝ) ≤
      dynamicIdeal (.inl (i,j)) (.inr (.inl k)) := by
  have hc := List.all_eq_true.mp (row_checks i j).1 k.val (List.mem_range.mpr k.isLt)
  change decide _ = true at hc
  rcases of_decide_eq_true hc with hz | ⟨_,h2,h5,hl,hlr,hr,hw⟩
  · rw [hz, Int.cast_zero, zero_div]
    change 0 ≤ singletonIntegralAtom _ _ _ _ / 2
    exact div_nonneg (MeasureTheory.integral_nonneg_of_ae
      (Filter.Eventually.of_forall singletonKernel_nonneg)) (by norm_num)
  · let l := left j k.val
    let r := right i j k.val
    have hl' : 0 < (l : ℝ) := by exact_mod_cast hl
    have hlr' : (l : ℝ) < (r : ℝ) := by exact_mod_cast hlr
    have hr' : (r : ℝ) < 1 := by exact_mod_cast hr
    have hcell := original_preimage i j k h2 h5
    have hsub : Ioo (l : ℝ) (r : ℝ) ⊆ singletonAmbient := by
      rw [← hcell]
      intro u hu
      exact W1Domain_subset i j hu.1
    have h1 : (1 : ℚ) ≤ r/l := (one_le_div (show 0 < l from hl)).2 hlr.le
    have h2log : (1 : ℚ) ≤ (1-l)/(1-r) :=
      (one_le_div (sub_pos.mpr (show r < 1 from hr))).2 (sub_le_sub_left hlr.le 1)
    have ha := series_lower h1
    have hb := series_lower h2log
    push_cast at ha hb
    have hw' : (archiveWeight i j k.val : ℝ)/(2^80 : ℝ) ≤
        ((logSeriesLower (r/l) 32 : ℝ)+(logSeriesLower ((1-l)/(1-r)) 32 : ℝ))/2 := by
      change (archiveWeight i j k.val : ℚ)/(2^80 : ℚ) ≤
        (logSeriesLower (r/l) 32 + logSeriesLower ((1-l)/(1-r)) 32)/2 at hw
      exact_mod_cast hw
    change _ ≤ singletonIntegralAtom _ _ _ _ / 2
    unfold singletonIntegralAtom
    rw [hcell]
    change _ ≤ singletonMass (Ioo (l : ℝ) (r : ℝ))/2
    rw [singletonMass_eq_original measurableSet_Ioo hsub, primitive hl' hlr'.le hr']
    linarith only [hw', ha, hb]

private theorem weighted_list (old : Table) (xs : List (ℕ × ℤ)) :
    (xs.map (fun w => read old false w.1 * w.2)).sum =
      ∑ k : Fin 200, old false k * weightAt xs k.val := by
  classical
  have one (w : ℕ × ℤ) :
      (∑ k : Fin 200, old false k * (if w.1 = k.val then w.2 else 0)) =
        read old false w.1 * w.2 := by
    by_cases h : w.1 < 200
    · let a : Fin 200 := ⟨w.1,h⟩
      rw [Finset.sum_eq_single a]
      · simp [a, read, h]
      · intro k _ hka
        have hk : w.1 ≠ k.val := fun he => hka (Fin.ext he.symm)
        simp [hk]
      · simp
    · rw [read, dif_neg h, zero_mul]
      apply Finset.sum_eq_zero
      intro k _
      have hk : w.1 ≠ k.val := fun he => h (he.symm ▸ k.isLt)
      simp [hk]
  induction xs with
  | nil => simp [weightAt]
  | cons w xs ih =>
      simp only [List.map_cons, List.sum_cons, weightAt] at ih ⊢
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib, one, ih]

/-- The archived ideal term expands before the genuine product and outer
floors. Its only W1 variable channel is the lower open-cell list. -/
theorem archived_w1_value (old : Table) (i : Fin 7) (j : Fin 10) :
    idealFeedbackValue old (.inl (i,j)) =
      ∑ k : Fin 200, ((archiveWeight i j k.val : ℝ)/(2^80 : ℝ)) *
        floorValue (old false) k := by
  have hrow := (row_checks i j).2
  have hnum : unroundedNumerator old (.inl (i,j)) =
      ∑ k : Fin 200, old false k * archiveWeight i j k.val := by
    unfold unroundedNumerator literalFeedbackProducts
    rw [hrow.1, List.map_nil, List.append_nil]
    exact weighted_list old _
  unfold idealFeedbackValue
  rw [hnum, hrow.2]
  change ((∑ k : Fin 200, old false k * archiveWeight i j k.val : ℤ) : ℝ) /
    (P2Selected430LiteralActionData.q : ℝ) / (1 : ℝ) / (2^80 : ℝ) = _
  have hq : (P2Selected430LiteralActionData.q : ℝ) = (2^80 : ℝ) := by
    norm_num [P2Selected430LiteralActionData.q]
  rw [hq, div_one, Int.cast_sum, Finset.sum_div, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k _
  rw [Int.cast_mul, floorValue]
  ring

/-- For every actual predecessor, all archived W1 lower feedback is
covered by the true continuous W1 integral row. The knot atoms of the
original closed lookup remain in the integral with nonnegative weight. -/
theorem immutable_w1_feedback_le_integral (i : Fin 7) (j : Fin 10) (g : Fin 430) :
    idealFeedbackValue (iterate g.val) (.inl (i,j)) ≤
      ∑ b : RowAtom, dynamicIdeal (.inl (i,j)) b * oldAtomValue (precedingH g) (precedingh g) b := by
  have hp (k : Fin 200) : 0 ≤ floorValue (precedingh g) k := by
    unfold floorValue
    exact div_nonneg (by exact_mod_cast iterate_nonneg g.val false k) (by positivity)
  have hkp (k : Fin 201) : 0 ≤ floorKnotValue (precedingh g) k := by
    unfold floorKnotValue
    split_ifs <;> first | exact hp _ | exact le_min (hp _) (hp _)
  rw [archived_w1_value]
  calc
    _ ≤ ∑ k : Fin 200, dynamicIdeal (.inl (i,j)) (.inr (.inl k)) *
        floorValue (precedingh g) k :=
      Finset.sum_le_sum (fun k _ => mul_le_mul_of_nonneg_right
        (archive_weight_le_dynamic_ideal i j k) (hp k))
    _ ≤ ∑ b : FloorAtom, dynamicIdeal (.inl (i,j)) (.inr b) * floorAtomValue (precedingh g) b := by
      rw [Fintype.sum_sum_type]
      apply le_add_of_nonneg_right
      apply Finset.sum_nonneg
      intro k _
      have hmass : 0 ≤ dynamicIdeal (.inl (i,j)) (.inr (.inr k)) :=
        div_nonneg (MeasureTheory.integral_nonneg_of_ae
          (Filter.Eventually.of_forall singletonKernel_nonneg)) (by norm_num)
      exact mul_nonneg hmass (hkp k)
    _ = _ := by
      conv_rhs => rw [Fintype.sum_sum_type]
      simp only [dynamicIdeal, oldAtomValue, zero_mul, Finset.sum_const_zero, zero_add]

/-- Every selected W1 position of the actual occurrence list carries the
same nonnegative parent Theta and original mark on both sides. -/
theorem actual_w1_feedback_le_integral (N n : ℕ) (k : Root) (t : ℝ) (p : ℕ)
    (g : Fin 430) (i : Fin 7) (j : Fin 10)
    (hN : 4 ≤ N) (ht : 0 ≤ t) (ht' : t ≤ 1/12)
    (hn : 1 / ((n : ℝ)+1) ≤ 11/384) (hp : p.Prime ∧ p.Coprime N)
    (hb : P2EnhancedLowerPrimeChildCarriers.physicalPrime N p ∈ rootBand k) :
    (∑ l ∈ selectedLevel N n k t p g (.inl (i,j)),
      occurrenceScale N n k t p g l * idealFeedbackValue (iterate g.val) (.inl (i,j))) ≤
    ∑ l ∈ selectedLevel N n k t p g (.inl (i,j)),
      occurrenceScale N n k t p g l *
        ∑ b : RowAtom, dynamicIdeal (.inl (i,j)) b * oldAtomValue (precedingH g) (precedingh g) b :=
  Finset.sum_le_sum (fun l _ => mul_le_mul_of_nonneg_left
    (immutable_w1_feedback_le_integral i j g) (occurrenceScale_nonneg N n k t p g l
      hN ht ht' hn hp hb))

/-- The arithmetic exception in a corrected W1 winning row consists of
its ordinary/switched base and the existing native row error. The
positive Q80 floor credit remains on the left. -/
theorem uniform_corrected_w1_gap_after_base {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
    ∀ (n : ℕ) (k : Root) (t : ℝ) (p : ℕ) (g : Fin 430) (i : Fin 7) (j : Fin 10),
      0 ≤ t → t ≤ 1/12 → 1 / ((n : ℝ)+1) ≤ 11/384 →
      (p.Prime ∧ p.Coprime N) → P2EnhancedLowerPrimeChildCarriers.physicalPrime N p ∈ rootBand k →
      let a : Original106Action := .inl (i,j)
      (∑ l ∈ selectedLevel N n k t p g a, levelDefect N n k t p g l +
        occurrenceScale N n k t p g l * feedbackRoundingLoss (iterate g.val) a) ≤
        (∑ l ∈ selectedLevel N n k t p g a, occurrenceScale N n k t p g l * baseValue a) +
          ε * levelTheta N n k t p g a := by
  obtain ⟨T,hT4,hT⟩ := uniform_level_bank_supply hε
  refine ⟨T,hT4,?_⟩
  intro N hNT n k t p g i j ht ht' hn hp hb
  let a : Original106Action := .inl (i,j)
  dsimp only
  have hf : fixedValue (iterate g.val true) a + idealFeedbackValue (iterate g.val) a ≤
      idealCellProfile (precedingH g) (precedingh g) a := by
    unfold idealCellProfile
    simp_rw [cellReadIdeal_split, add_mul]
    rw [Finset.sum_add_distrib, readFixed_value, one_mul]
    exact add_le_add_left (immutable_w1_feedback_le_integral i j g) _
  have he := (hT N hNT n k t ht ht' hn p hp hb g a).2.1
  apply le_trans _ (add_le_add_left he _)
  unfold levelAppliedError
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro l hl
  have hc := bank_level_defect_le_candidate N n k t p g a
    (hT4.trans hNT) ht ht' hn hp hb l hl
  have hscale := occurrenceScale_nonneg N n k t p g l (hT4.trans hNT) ht ht' hn hp hb
  let F := idealCellProfile (precedingH g) (precedingh g) a
  let θ := occurrenceTheta N n k t p g l
  let child := childTerm N n k t p g l
  have habs : θ*F-child ≤ |child-θ*F| := by
    rw [abs_sub_comm]
    exact le_abs_self _
  have hmabs := mul_le_mul_of_nonneg_left habs (mark_pos (levelOccurrence l)).le
  calc
    _ ≤ bankCandidateGap N n k t p g a l +
          occurrenceScale N n k t p g l * feedbackRoundingLoss (iterate g.val) a :=
      add_le_add_right hc _
    _ = occurrenceScale N n k t p g l * baseValue a +
          (occurrenceScale N n k t p g l *
            (fixedValue (iterate g.val true) a + idealFeedbackValue (iterate g.val) a) -
           levelMark l * child) := by
      rw [ideal_feedback_exact (iterate g.val) a]
      unfold bankCandidateGap occurrenceScale occurrenceTheta
      dsimp only [child]
      ring
    _ ≤ occurrenceScale N n k t p g l * baseValue a +
          (occurrenceScale N n k t p g l * F - levelMark l * child) :=
      add_le_add_left (sub_le_sub_right (mul_le_mul_of_nonneg_left hf hscale) _) _
    _ ≤ _ := by
      change _ ≤ occurrenceScale N n k t p g l * baseValue a + levelMark l * |child-θ*F|
      apply add_le_add_left
      change levelMark l * θ * F - levelMark l * child ≤ levelMark l * |child-θ*F|
      change levelMark l * (θ*F-child) ≤ levelMark l * |child-θ*F| at hmabs
      linarith only [hmabs]


end
end ImbalancedChen.Part5OriginalH430W1ArchivedFeedback

