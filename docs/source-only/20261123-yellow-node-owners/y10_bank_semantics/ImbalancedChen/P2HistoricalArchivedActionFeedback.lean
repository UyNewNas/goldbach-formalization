import ImbalancedChen.P2HistoricalScheduledPointReads
import ImbalancedChen.Part5OriginalH430W2UpperBankPayment

/-! Coefficients shared by the two archives are reused with the actual
H248 predecessor. Baselines and predecessor tables are stage-specific. -/
namespace ImbalancedChen.P2HistoricalArchivedActionFeedback

noncomputable section
open MeasureTheory
open scoped Classical BigOperators
open P2TableActionSourceOnly P2SimultaneousTableSourceOnly (Table Nonnegative)
open P2HistoricalSourceJSON P2Historical248Authentication P2HistoricalScheduledPointReads
open P2HistoricalLowerBankAncestry (iterate_nonnegative)
open P2Selected430LiteralActionData (rows)
open P5OriginalActionMassBound P5OriginalFeedbackDomains
open Part5OriginalUpsilon5CausalDictionary (FloorAtom floorValue floorKnotValue floorAtomValue)
open P2OriginalBankChildPrimeMass (singletonTop)
open Part5OriginalH430BankSlotTargets (slotOfAction)
open Part5OriginalH430LiteralBankBudget
  (singletonIntegralAtom pairIntegralAtom singletonIntegralAtom_value pairIntegralAtom_value)
open P2OriginalBankOldProfilePassage (singleOldIntegral pairOldIntegral)
open Part5OriginalH430W2UpperPolygons (parameterQ)
open Part5OriginalH430W2UpperArchiveData (weights)
open Part5OriginalH430W2UpperWeights (weightAt grouped original_lists)

abbrev Weight := P2OriginalW2CandidateIntegerABI.WeightRow
abbrev Slot := Fin 7 × Fin 10
abbrev Tagged := Value × P2OriginalW2CandidateIntegerABI.Action

def encode (xs : List Weight) : List (ℕ × ℤ) := xs.map fun w => (w.index.val, w.lower)

private def matchesW1 (a : SourceW1) (z : Slot) : Bool := decide
  (a.s = 12/5 + (z.1.val : ℚ)/10 ∧ a.s0 = 16/5 + (z.2.val : ℚ)/5 ∧
    encode a.feedback = (rows (slotOfAction (.inl z))).lowerWeights)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem original_w1_lists :
    w1Original.all (fun a => (List.finRange 7).any (fun i =>
      (List.finRange 10).any (fun j => matchesW1 a (i,j)))) = true := by decide

private theorem retained_w1_lists (x : SourceW1 × Value) (xs : List SourceW1) (ys : List Value)
    (hx : x ∈ xs.zip ys) : x.1 ∈ xs := by
  induction xs generalizing ys with
  | nil => simp at hx
  | cons a xs ih =>
    cases ys with
    | nil => simp at hx
    | cons b ys =>
      change x ∈ (a,b) :: xs.zip ys at hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem a (ih ys hx)

theorem actual_w1_list (g : ℕ) {a : SourceW1} (ha : a ∈ sourceW1Schedule g) :
    ∃ i : Fin 7, ∃ j : Fin 10,
      a.s = 12/5 + (i.val : ℚ)/10 ∧ a.s0 = 16/5 + (j.val : ℚ)/5 ∧
      encode a.feedback = (rows (slotOfAction (.inl (i,j)))).lowerWeights := by
  have hm : (List.finRange 7).any (fun i =>
      (List.finRange 10).any (fun j => matchesW1 a (i,j))) = true := by
    unfold sourceW1Schedule at ha
    split at ha
    · exact List.all_eq_true.mp original_w1_lists a ha
    · obtain ⟨x,hx,rfl⟩ := List.mem_map.mp ha
      have h := List.all_eq_true.mp original_w1_lists x.1 (retained_w1_lists x _ _ hx)
      simpa only [matchesW1] using h
  obtain ⟨i,_,hi⟩ := List.any_eq_true.mp hm
  obtain ⟨j,_,hj⟩ := List.any_eq_true.mp hi
  exact ⟨i,j,of_decide_eq_true hj⟩

def pairLane (a : P2OriginalW2CandidateIntegerABI.Action) (k : Fin 4) : List Weight :=
  (a.pairRows[k.val]?).getD []

private def matchesW2 (b : Value) (j : Fin 36) : Bool :=
  decide (parameters b = List.ofFn (parameterQ j) ∧
    encode (readW2 b).negativeRows.flatten = (rows (slotOfAction (.inr j))).lowerWeights ∧
    encode (readW2 b).pairRows.flatten = grouped j ∧
    (readW2 b).negativeRows.length = 3 ∧ (readW2 b).pairRows.length = 4) &&
  (List.finRange 4).all (fun k => decide (encode (pairLane (readW2 b) k) = weights j k))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem original_w2_lists :
    (oldRows ++ addedRows).all (fun b => (List.finRange 36).any (matchesW2 b)) = true := by decide

private theorem tagged_fields {vs : List Value} {b : Tagged} (hb : b ∈ tag vs) :
    b.1 ∈ vs ∧ b.2.negativeRows = (readW2 b.1).negativeRows ∧
      b.2.pairRows = (readW2 b.1).pairRows := by
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hb
  exact ⟨hv,rfl,rfl⟩

private theorem repriced_fields {vs us : List Value} {b : Tagged} (hb : b ∈ reprice vs us) :
    b.1 ∈ vs ∧ b.2.negativeRows = (readW2 b.1).negativeRows ∧
      b.2.pairRows = (readW2 b.1).pairRows := by
  induction vs generalizing us with
  | nil => simp [reprice] at hb
  | cons v vs ih =>
    cases us with
    | nil => simp [reprice] at hb
    | cons u us =>
      change b ∈ _ :: reprice vs us at hb
      rcases List.mem_cons.mp hb with rfl | hb
      · exact ⟨List.mem_cons_self,rfl,rfl⟩
      · obtain ⟨hv,hl,hu⟩ := ih hb
        exact ⟨List.mem_cons_of_mem v hv,hl,hu⟩

private theorem historical_w2_fields (g : ℕ) {b : Tagged} (hb : b ∈ taggedW2 g) :
    b.1 ∈ oldRows ++ addedRows ∧ b.2.negativeRows = (readW2 b.1).negativeRows ∧
      b.2.pairRows = (readW2 b.1).pairRows := by
  unfold taggedW2 at hb
  split_ifs at hb
  · simp at hb
  · obtain ⟨hm,hl,hu⟩ := tagged_fields hb
    exact ⟨List.mem_append.mpr (Or.inl hm),hl,hu⟩
  · obtain ⟨hm,hl,hu⟩ := repriced_fields hb
    exact ⟨List.mem_append.mpr (Or.inl hm),hl,hu⟩
  · obtain ⟨hm,hl,hu⟩ := repriced_fields hb
    exact ⟨List.mem_append.mpr (Or.inl hm),hl,hu⟩
  · rcases List.mem_append.mp hb with h | h
    · obtain ⟨hm,hl,hu⟩ := repriced_fields h
      exact ⟨List.mem_append.mpr (Or.inl hm),hl,hu⟩
    · obtain ⟨hm,hl,hu⟩ := tagged_fields h
      exact ⟨List.mem_append.mpr (Or.inr hm),hl,hu⟩

/-- Repricing preserves the three original singleton lists in their order
and each of the four separate original ordered pair lists. -/
theorem actual_w2_lists (g : ℕ) {b : Tagged} (hb : b ∈ taggedW2 g) :
    ∃ j : Fin 36, parameters b.1 = List.ofFn (parameterQ j) ∧
      encode b.2.negativeRows.flatten = (rows (slotOfAction (.inr j))).lowerWeights ∧
      encode b.2.pairRows.flatten = grouped j ∧ b.2.negativeRows.length = 3 ∧
      b.2.pairRows.length = 4 ∧ ∀ k : Fin 4, encode (pairLane b.2 k) = weights j k := by
  obtain ⟨hv,hl,hu⟩ := historical_w2_fields g hb
  obtain ⟨j,_,hj⟩ := List.any_eq_true.mp (List.all_eq_true.mp original_w2_lists b.1 hv)
  obtain ⟨hc,hr⟩ := Bool.and_eq_true.mp hj
  obtain ⟨hp,hls,hus,hn,hm⟩ := of_decide_eq_true hc
  refine ⟨j,hp,by rw [hl,hls],by rw [hu,hus],by rw [hl,hn],by rw [hu,hm],?_⟩
  intro k
  simpa only [pairLane,hu] using
    (of_decide_eq_true (List.all_eq_true.mp hr k (List.mem_finRange k)) :
      encode (pairLane (readW2 b.1) k) = weights j k)

private theorem rounded_numerator (old : Table) (side : Bool) (xs : List Weight) :
    sourceWeightSum old side xs * (tableQ : ℤ) ≤
      ∑ i : Fin 200, old side i * weightAt (encode xs) i.val := by
  have one (r : Weight) : (∑ i : Fin 200, old side i *
      (if r.index.val = i.val then r.lower else 0)) = old side r.index * r.lower := by
    rw [Finset.sum_eq_single r.index]
    · simp
    · intro i _ hi
      simp [show r.index.val ≠ i.val from fun h => hi (Fin.ext h.symm)]
    · simp
  induction xs with
  | nil => simp [sourceWeightSum,encode,weightAt]
  | cons r xs ih =>
    have split (i : Fin 200) : weightAt (encode (r::xs)) i.val =
        (if r.index.val = i.val then r.lower else 0) + weightAt (encode xs) i.val := by
      simp [encode,weightAt]
    simp_rw [split,mul_add]
    rw [Finset.sum_add_distrib,one]
    change (old side r.index * r.lower / (tableQ : ℤ) + sourceWeightSum old side xs) *
      (tableQ : ℤ) ≤ _
    rw [add_mul]
    exact add_le_add (Int.ediv_mul_le _ (show (tableQ : ℤ) ≠ 0 by exact_mod_cast tableQ_pos.ne')) ih

private theorem rounded_le_cells (old : Table) (side : Bool) (xs : List Weight) :
    (sourceWeightSum old side xs : ℝ) / tableQ ≤
      ∑ i : Fin 200, ((weightAt (encode xs) i.val : ℝ) / (2^80 : ℝ)) * floorValue (old side) i := by
  have hq : (0 : ℝ) < tableQ := by exact_mod_cast tableQ_pos
  have hc : (sourceWeightSum old side xs : ℝ) * (tableQ : ℝ) ≤
      ∑ i : Fin 200, (old side i : ℝ) * (weightAt (encode xs) i.val : ℝ) := by
    exact_mod_cast rounded_numerator old side xs
  have hid : (∑ i : Fin 200, (old side i : ℝ) * (weightAt (encode xs) i.val : ℝ)) /
        ((tableQ : ℝ) * (tableQ : ℝ)) =
      ∑ i : Fin 200, ((weightAt (encode xs) i.val : ℝ) / (2^80 : ℝ)) * floorValue (old side) i := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    rw [show (tableQ : ℝ) = (2^80 : ℝ) by norm_num [tableQ],floorValue]
    ring
  rw [← hid]
  apply (le_div_iff₀ (mul_pos hq hq)).mpr
  calc
    _ = (sourceWeightSum old side xs : ℝ) * (tableQ : ℝ) := by field_simp [hq.ne'] <;> ring
    _ ≤ _ := hc

private theorem add_knot_terms (old : Fin 200 → ℤ) (h : ∀ i, 0 ≤ old i)
    (coeff : FloorAtom → ℝ) (hc : ∀ k : Fin 201, 0 ≤ coeff (.inr k)) :
    (∑ i : Fin 200, coeff (.inl i) * floorValue old i) ≤
      ∑ b : FloorAtom, coeff b * floorAtomValue old b := by
  have hcell (i : Fin 200) : 0 ≤ floorValue old i :=
    div_nonneg (by exact_mod_cast h i) (by positivity)
  have hk (j : Fin 201) : 0 ≤ floorKnotValue old j := by
    unfold floorKnotValue
    split_ifs <;> first | exact hcell _ | exact le_min (hcell _) (hcell _)
  rw [Fintype.sum_sum_type]
  exact le_add_of_nonneg_right (Finset.sum_nonneg fun j _ => mul_nonneg (hc j) (hk j))

private theorem singleton_atom_nonneg (l r s : ℝ) (b : FloorAtom) :
    0 ≤ singletonIntegralAtom l r s b :=
  integral_nonneg_of_ae (Filter.Eventually.of_forall singletonKernel_nonneg)

private theorem pair_atom_nonneg (p : W2Parameters) (k : Fin 4) (b : FloorAtom) :
    0 ≤ pairIntegralAtom p k b :=
  integral_nonneg_of_ae (Filter.Eventually.of_forall pairKernel_nonneg)

/-- The W1 singleton feedback with its half in the coefficient. -/
def w1Feedback (i : Fin 7) (j : Fin 10) (oldh : Fin 200 → ℤ) : ℝ :=
  ∑ b : FloorAtom, (singletonIntegralAtom (1/W1Anchor j) (1/W1Target i) (W1Anchor j) b/2) *
    floorAtomValue oldh b

/-- Three actual W2 singleton contributions, with the action's one fifth. -/
def w2SingletonFeedback (j : Fin 36) (oldh : Fin 200 → ℤ) : ℝ :=
  ∑ b : FloorAtom, ((∑ k : Fin 3, singletonIntegralAtom (a0 (originalW2At j))
    (singletonTop (originalW2At j) k) (originalW2At j).s0 b)/5) * floorAtomValue oldh b

/-- A labelled good-pair contribution before the W2 divisor. -/
def w2PairFeedback (j : Fin 36) (k : Fin 4) (oldH : Fin 200 → ℤ) : ℝ :=
  ∑ b : FloorAtom, pairIntegralAtom (originalW2At j) k b * floorAtomValue oldH b

theorem w1Feedback_eq_integral (i : Fin 7) (j : Fin 10) (oldh : Fin 200 → ℤ) :
    w1Feedback i j oldh = singleOldIntegral (1/W1Anchor j) (1/W1Target i) (W1Anchor j) oldh / 2 := by
  unfold w1Feedback
  simp_rw [div_mul_eq_mul_div]
  rw [← Finset.sum_div, singletonIntegralAtom_value (W1Domain_subset i j)]

theorem w2SingletonFeedback_eq_integral (j : Fin 36) (oldh : Fin 200 → ℤ) :
    w2SingletonFeedback j oldh = (∑ k : Fin 3, singleOldIntegral
      (a0 (originalW2At j)) (singletonTop (originalW2At j) k) (originalW2At j).s0 oldh)/5 := by
  have hp := originalRepairedW2Bank_geometry _ (originalW2At_mem j)
  unfold w2SingletonFeedback
  simp_rw [div_mul_eq_mul_div]
  rw [← Finset.sum_div]
  congr 1
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply singletonIntegralAtom_value
  have he : Set.Ioo (a0 (originalW2At j)) (singletonTop (originalW2At j) k) =
      W2SingletonDomain (originalW2At j) k := by fin_cases k <;> rfl
  rw [he]
  exact W2SingletonDomain_subset hp k

theorem w2PairFeedback_eq_integral (j : Fin 36) (k : Fin 4) (oldH : Fin 200 → ℤ) :
    w2PairFeedback j k oldH = pairOldIntegral (originalW2At j) k oldH :=
  pairIntegralAtom_value (originalRepairedW2Bank_geometry _ (originalW2At_mem j)) k oldH

private theorem w1_weighted (old : Table) (ho : Nonnegative old) (a : SourceW1)
    (i : Fin 7) (j : Fin 10) (he : encode a.feedback = (rows (slotOfAction (.inl (i,j)))).lowerWeights) :
    (sourceWeightSum old false a.feedback : ℝ)/tableQ ≤ w1Feedback i j (old false) := by
  have h := rounded_le_cells old false a.feedback
  rw [he] at h
  apply h.trans
  apply le_trans (Finset.sum_le_sum (fun k _ => ?_))
    (add_knot_terms _ (ho false) _ (fun k => div_nonneg (singleton_atom_nonneg _ _ _ _) (by norm_num)))
  apply mul_le_mul_of_nonneg_right _ (div_nonneg (by exact_mod_cast ho false k) (by positivity))
  exact Part5OriginalH430W1ArchivedFeedback.archive_weight_le_dynamic_ideal i j k

private theorem w2_singletons_weighted (old : Table) (ho : Nonnegative old)
    (b : Tagged) (j : Fin 36)
    (he : encode b.2.negativeRows.flatten = (rows (slotOfAction (.inr j))).lowerWeights) :
    (sourceWeightSum old false b.2.negativeRows.flatten : ℝ) / tableQ / 5 ≤
      w2SingletonFeedback j (old false) := by
  have h := rounded_le_cells old false b.2.negativeRows.flatten
  rw [he] at h
  apply (div_le_div_of_nonneg_right h (by norm_num : (0 : ℝ) ≤ 5)).trans
  rw [Finset.sum_div]
  apply le_trans (Finset.sum_le_sum (fun k _ => ?_))
    (add_knot_terms _ (ho false) _ (fun k => div_nonneg
      (Finset.sum_nonneg fun t _ => singleton_atom_nonneg _ _ _ _) (by norm_num)))
  calc
    _ = ((weightAt (rows (slotOfAction (.inr j))).lowerWeights k.val : ℝ) / (2^80 : ℝ)/5) *
        floorValue (old false) k := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (Part5OriginalH430W2ArchivedSingletons.archive_weight_le_singletons j k)
      (div_nonneg (by exact_mod_cast ho false k) (by positivity))

private theorem w2_pair_weighted (old : Table) (ho : Nonnegative old)
    (j : Fin 36) (k : Fin 4) (xs : List Weight) (he : encode xs = weights j k) :
    (sourceWeightSum old true xs : ℝ)/tableQ ≤ w2PairFeedback j k (old true) := by
  have h := rounded_le_cells old true xs
  rw [he] at h
  apply h.trans
  apply le_trans (Finset.sum_le_sum (fun i _ => ?_))
    (add_knot_terms _ (ho true) _ (fun _ => pair_atom_nonneg _ _ _))
  exact mul_le_mul_of_nonneg_right
    (Part5OriginalH430W2UpperBankPayment.all36_four_original_pair_measures j k i)
    (div_nonneg (by exact_mod_cast ho true i) (by positivity))

/-- The actual calendar baseline is outside the archived lower-profile term. -/
theorem w1_candidate_le_old_profile (g : ℕ) {a : SourceW1} (ha : a ∈ sourceW1Schedule g) :
    ∃ i : Fin 7, ∃ j : Fin 10,
      a.s = 12/5 + (i.val : ℚ)/10 ∧ a.s0 = 16/5 + (j.val : ℚ)/5 ∧
      (sourceW1Value (outputAt g) a : ℝ)/tableQ ≤ (a.effectiveBase : ℝ)/tableQ +
        (outputAt g true a.pointIndex : ℝ)/tableQ + w1Feedback i j (outputAt g false) := by
  obtain ⟨i,j,hs,ha',he⟩ := actual_w1_list g ha
  refine ⟨i,j,hs,ha',?_⟩
  have hw := w1_weighted (outputAt g) (iterate_nonnegative designatedW1 designatedW2 g) a i j he
  simpa only [sourceW1Value,Int.cast_add,add_div] using add_le_add_left hw
    ((a.effectiveBase : ℝ)/tableQ + (outputAt g true a.pointIndex : ℝ)/tableQ)

/-- Round every old product separately, and keep the three singleton
lists and four good-pair lanes with the same old arrays. -/
theorem w2_feedback_le_old_profiles (g : ℕ) {b : Tagged} (hb : b ∈ taggedW2 g) :
    ∃ j : Fin 36, parameters b.1 = List.ofFn (parameterQ j) ∧
      (sourceWeightSum (outputAt g) false b.2.negativeRows.flatten : ℝ)/tableQ/5 ≤
        w2SingletonFeedback j (outputAt g false) ∧
      ∀ k : Fin 4, (sourceWeightSum (outputAt g) true (pairLane b.2 k) : ℝ)/tableQ ≤
        w2PairFeedback j k (outputAt g true) := by
  obtain ⟨j,hp,hl,_,_,_,hu⟩ := actual_w2_lists g hb
  have ho := iterate_nonnegative designatedW1 designatedW2 g
  exact ⟨j,hp,w2_singletons_weighted (outputAt g) ho b j hl,
    fun k => w2_pair_weighted (outputAt g) ho j k _ (hu k)⟩

private theorem pair_weight_sum (j : Fin 36) (i : Fin 200) :
    weightAt (grouped j) i.val = ∑ k : Fin 4, weightAt (weights j k) i.val := by
  simp [grouped,weightAt,Fin.sum_univ_succ] <;> ring

private theorem w2_all_pairs_weighted (old : Table) (ho : Nonnegative old)
    (j : Fin 36) (xs : List Weight) (he : encode xs = grouped j) :
    (sourceWeightSum old true xs : ℝ)/tableQ ≤ ∑ k : Fin 4, w2PairFeedback j k (old true) := by
  have h := rounded_le_cells old true xs
  rw [he] at h
  apply h.trans
  have hsum : (∑ i : Fin 200, ((weightAt (grouped j) i.val : ℝ) / (2^80 : ℝ)) *
      floorValue (old true) i) = ∑ k : Fin 4, ∑ i : Fin 200,
      ((weightAt (weights j k) i.val : ℝ) / (2^80 : ℝ)) * floorValue (old true) i := by
    simp_rw [pair_weight_sum,Int.cast_sum,Finset.sum_div,Finset.sum_mul]
    exact Finset.sum_comm
  rw [hsum]
  apply Finset.sum_le_sum
  intro k _
  apply le_trans (Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right
    (Part5OriginalH430W2UpperBankPayment.all36_four_original_pair_measures j k i)
    (div_nonneg (by exact_mod_cast ho true i) (by positivity))))
  exact add_knot_terms _ (ho true) _ (fun i => pair_atom_nonneg _ _ _)

/-- The original W2 candidate, using one outer integer fifth and its own
unchanged baseline and point numerator. -/
theorem w2_candidate_le_old_profile (g : ℕ) {b : Tagged} (hb : b ∈ taggedW2 g) :
    ∃ j : Fin 36, parameters b.1 = List.ofFn (parameterQ j) ∧
      (sourceW2Value (outputAt g) b.2 : ℝ)/tableQ ≤ (b.2.base : ℝ)/tableQ +
        (sourcePointSum (outputAt g) b.2.points : ℝ)/tableQ/5 +
        w2SingletonFeedback j (outputAt g false) +
        (∑ k : Fin 4, w2PairFeedback j k (outputAt g true))/5 := by
  obtain ⟨j,hp,hl,hu,_,_,_⟩ := actual_w2_lists g hb
  refine ⟨j,hp,?_⟩
  let old := outputAt g
  let pts := sourcePointSum old b.2.points
  let ll := sourceWeightSum old false b.2.negativeRows.flatten
  let uu := sourceWeightSum old true b.2.pairRows.flatten
  have ho := iterate_nonnegative designatedW1 designatedW2 g
  have hs := w2_singletons_weighted old ho b j hl
  have hpair := div_le_div_of_nonneg_right (w2_all_pairs_weighted old ho j _ hu)
    (by norm_num : (0 : ℝ) ≤ 5)
  have hoQ : (0 : ℝ) ≤ tableQ := by positivity
  have hn : (((pts+ll+uu)/5 : ℤ) : ℝ) * (5 : ℝ) ≤ ((pts+ll+uu : ℤ) : ℝ) := by
    exact_mod_cast Int.ediv_mul_le (pts+ll+uu) (show (5 : ℤ) ≠ 0 by decide)
  have hm := div_le_div_of_nonneg_right ((le_div_iff₀ (by norm_num : (0 : ℝ)<5)).mpr hn) hoQ
  have hre : (((pts+ll+uu : ℤ) : ℝ)/5)/tableQ =
      (pts : ℝ)/tableQ/5 + (ll : ℝ)/tableQ/5 + (uu : ℝ)/tableQ/5 := by
    push_cast
    ring
  rw [hre] at hm
  change (((b.2.base + (pts+ll+uu)/5 : ℤ) : ℝ)/tableQ) ≤ _
  rw [Int.cast_add,add_div]
  change _ ≤ (b.2.base : ℝ)/tableQ + (pts : ℝ)/tableQ/5 + _ + _
  change (ll : ℝ)/tableQ/5 ≤ _ at hs
  change (uu : ℝ)/tableQ/5 ≤ _ at hpair
  linarith only [hm,hs,hpair]

end
end ImbalancedChen.P2HistoricalArchivedActionFeedback
