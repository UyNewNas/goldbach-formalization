import ImbalancedChen.Part5OriginalH430W1ArchivedFeedback

/-! The three W2 lower-singleton channels at all 36 original actions.
A grid cell can occur in several gamma lists. Its archived weight is the
sum of those genuine occurrences; its comparison measure is the sum of
the three corresponding kernel integrals. The original outer divisor
is five. The separate upper pair channel retains its own archived list. -/

namespace ImbalancedChen.Part5OriginalH430W2ArchivedSingletons

noncomputable section
open Set MeasureTheory
open scoped BigOperators
open Certificates (logSeriesLower logSeriesUpper RationalLogCertificate)
open P2Selected430CausalOccurrenceExporter (Table iterate read)
open P2Selected430LiteralActionData (rows)
open P2OriginalBankChildPrimeMass (singletonTop)
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
open Part5OriginalH430CorrectedWinningSource Part5OriginalH430ActualNextTableSignedSourceResidual
open Part5OriginalH430ActualSelectedRowBudget

/-- Rational tuples in original (s,s0,phi1,phi2,phi3) order. The real
coercion lemma verifies s0 and all three required cutoff endpoints of
the production records. The third coordinate is unused by singletons. -/
private def parameterQ : Fin 36 → Fin 5 → ℚ :=
  ![![11/5, 227/50, 353/100, 29/10, 61/25],
    ![11/5, 24/5, 353/100, 29/10, 47/20],
    ![21/10, 24/5, 353/100, 29/10, 117/50],
    ![101/50, 9707/2000, 89/25, 14663/5000, 11667/5000],
    ![51/25, 46871/10000, 18297/5000, 28913/10000, 11909/5000],
    ![103/50, 24/5, 7119/2000, 2931/1000, 4679/2000],
    ![52/25, 1863/400, 181/50, 7253/2500, 23819/10000],
    ![21/10, 46399/10000, 18099/5000, 1451/500, 23813/10000],
    ![21/10, 47873/10000, 89/25, 14623/5000, 23379/10000],
    ![53/25, 46681/10000, 35999/10000, 29037/10000, 2977/1250],
    ![107/50, 119/25, 17897/5000, 1822/625, 23317/10000],
    ![54/25, 46397/10000, 179/50, 29109/10000, 2977/1250],
    ![11/5, 23199/5000, 89/25, 14597/5000, 4763/2000],
    ![11/5, 47323/10000, 17799/5000, 7297/2500, 4659/2000],
    ![56/25, 45799/10000, 89/25, 1457/500, 2977/1250],
    ![56/25, 2911/625, 17899/5000, 233/80, 5843/2500],
    ![57/25, 45393/10000, 179/50, 3641/1250, 2977/1250],
    ![23/10, 5599/1250, 179/50, 729/250, 11907/5000],
    ![58/25, 5573/1250, 18/5, 29101/10000, 2977/1250],
    ![58/25, 45569/10000, 18099/5000, 29057/10000, 11619/5000],
    ![59/25, 2209/500, 18/5, 2907/1000, 2977/1250],
    ![12/5, 42999/10000, 18/5, 29131/10000, 24077/10000],
    ![61/25, 20797/5000, 181/50, 29193/10000, 3053/1250],
    ![61/25, 8319/2000, 18/5, 7289/2500, 24471/10000],
    ![62/25, 4079/1000, 179/50, 29231/10000, 12433/5000],
    ![5/2, 203/50, 7119/2000, 5837/2000, 25063/10000],
    ![63/25, 40587/10000, 177/50, 2921/1000, 1263/500],
    ![64/25, 191/50, 17699/5000, 5873/2000, 25619/10000],
    ![64/25, 20297/5000, 34999/10000, 14601/5000, 12827/5000],
    ![13/5, 81/20, 17293/5000, 5843/2000, 1628/625],
    ![66/25, 40501/10000, 33999/10000, 29213/10000, 13221/5000],
    ![67/25, 179/50, 86/25, 29529/10000, 13407/5000],
    ![67/25, 10127/2500, 84/25, 14649/5000, 26837/10000],
    ![68/25, 81/20, 33/10, 29343/10000, 1702/625],
    ![69/25, 81/20, 163/50, 29343/10000, 13813/5000],
    ![14/5, 81/20, 161/50, 5883/2000, 28021/10000]]

private def gridQ (k : ℕ) : ℚ := 1+(k : ℚ)/50
private def lowQ (j : Fin 36) : ℚ := 1/parameterQ j 1
private def topQ (j : Fin 36) : Fin 3 → ℚ :=
  ![1/parameterQ j 0, 1/parameterQ j 3, 1/parameterQ j 4]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem coordinates (j : Fin 36) :
    (parameterQ j 1 : ℝ) = (originalW2At j).s0 ∧
      (lowQ j : ℝ) = a0 (originalW2At j) ∧
      ∀ t : Fin 3, (topQ j t : ℝ) = singletonTop (originalW2At j) t := by
  fin_cases j <;>
    (refine ⟨?_,?_,?_⟩ <;>
      first | (intro t; fin_cases t <;> norm_num [parameterQ, lowQ, topQ, originalW2At,
          originalRepairedW2Bank, singletonTop, a0, a2, a3, P5OriginalActionMassBound.b])
            | norm_num [parameterQ, lowQ, originalW2At, originalRepairedW2Bank, a0])

private def left (j : Fin 36) (k : ℕ) : ℚ :=
  max (lowQ j) (1-gridQ (k+1)/parameterQ j 1)
private def right (j : Fin 36) (t : Fin 3) (k : ℕ) : ℚ :=
  min (topQ j t) (1-gridQ k/parameterQ j 1)

private def laneLower (j : Fin 36) (t : Fin 3) (k : ℕ) : ℚ :=
  let l := left j k
  let r := right j t k
  if 2 ≤ gridQ k ∧ gridQ (k+1) ≤ 5 ∧ 0 < l ∧ l < r ∧ r < 1 then
    logSeriesLower (r/l) 32 + logSeriesLower ((1-l)/(1-r)) 32
  else 0

private def weightAt (xs : List (ℕ × ℤ)) (k : ℕ) : ℤ :=
  (xs.map (fun w => if w.1 = k then w.2 else 0)).sum

/-- Every occurrence of the cell in the actual flattened lower list
contributes, including two or three occurrences in different gamma rows. -/
def archiveWeight (j : Fin 36) (k : ℕ) : ℤ :=
  weightAt (rows (slotOfAction (.inr j))).lowerWeights k

private def cellChecks (j : Fin 36) (k : ℕ) : Bool :=
  decide ((archiveWeight j k : ℚ)/(2^80 : ℚ) ≤ ∑ t : Fin 3, laneLower j t k)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem original_checks (j : Fin 36) :
    (List.range 200).all (cellChecks j) = true ∧
      (rows (slotOfAction (.inr j))).divisor = 5 ∧
      (rows (slotOfAction (.inr j))).lowerWeights.all
        (fun w => decide (w.1 < 200 ∧ 0 < w.2)) = true := by
  fin_cases j <;> decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- Counts of literal occurrences in the original three and expanded 33
singleton lists. Repeated cell indices in different gamma lanes count again. -/
theorem original_w2_singleton_census :
    (∑ j : Fin 36, if j.val < 3 then (rows (slotOfAction (.inr j))).lowerWeights.length else 0) = 424 ∧
    (∑ j : Fin 36, if 3 ≤ j.val then (rows (slotOfAction (.inr j))).lowerWeights.length else 0) = 3626 := by
  decide

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


private theorem preimage (j : Fin 36) (t : Fin 3) (k : Fin 200)
    (h2 : 2 ≤ gridQ k.val) (h5 : gridQ (k.val+1) ≤ 5) :
    Ioo (a0 (originalW2At j)) (singletonTop (originalW2At j) t) ∩
      tablePullback true (singletonProfile (originalW2At j).s0) (.inl k) =
        Ioo (left j k.val : ℝ) (right j t k.val : ℝ) := by
  let A := (originalW2At j).s0
  have ha : 0 < A := W2_anchor_positive (originalRepairedW2Bank_geometry _ (originalW2At_mem j))
  have grid (q : ℕ) : (gridQ q : ℝ) = floorGrid q := by simp [gridQ, floorGrid]
  have h2' : (2 : ℝ) ≤ floorGrid k.val := by rw [← grid]; exact_mod_cast h2
  have h5' : floorGrid (k.val+1) ≤ (5 : ℝ) := by rw [← grid]; exact_mod_cast h5
  have hl : (left j k.val : ℝ) = max (a0 (originalW2At j)) (1-floorGrid (k.val+1)/A) := by
    simp [left, grid, (coordinates j).1, (coordinates j).2.1, A]
  have hr : (right j t k.val : ℝ) =
      min (singletonTop (originalW2At j) t) (1-floorGrid k.val/A) := by
    simp [right, grid, (coordinates j).1, (coordinates j).2.2 t, A]
  rw [hl, hr]
  ext u
  have hi (x : ℝ) : 1-x/A < u ↔ A*(1-u) < x := by
    calc
      _ ↔ 1-u < x/A := by constructor <;> intro h <;> linarith only [h]
      _ ↔ _ := by rw [lt_div_iff₀ ha, mul_comm]
  have lo (x : ℝ) : u < 1-x/A ↔ x < A*(1-u) := by
    calc
      _ ↔ x/A < 1-u := by constructor <;> intro h <;> linarith only [h]
      _ ↔ _ := by rw [div_lt_iff₀ ha, mul_comm]
  change ((_ < u ∧ u < _) ∧ (2 ≤ A*(1-u) ∧ A*(1-u) ≤ 5) ∧
    floorGrid k.val < A*(1-u) ∧ A*(1-u) < floorGrid (k.val+1)) ↔
    (max _ _ < u ∧ u < min _ _)
  rw [max_lt_iff, lt_min_iff, hi, lo]
  constructor
  · rintro ⟨⟨hl',hr'⟩,_,hc,hb⟩
    exact ⟨⟨hl',hb⟩,hr',hc⟩
  · rintro ⟨⟨hl',hb⟩,hr',hc⟩
    exact ⟨⟨hl',hr'⟩,⟨h2'.trans hc.le, hb.le.trans h5'⟩,hc,hb⟩

private theorem lane_le (j : Fin 36) (t : Fin 3) (k : Fin 200) :
    (laneLower j t k.val : ℝ) ≤ singletonIntegralAtom (a0 (originalW2At j))
      (singletonTop (originalW2At j) t) (originalW2At j).s0 (.inl k) := by
  unfold laneLower
  split_ifs with h
  · obtain ⟨h2,h5,hl,hlr,hr⟩ := h
    let l := left j k.val
    let r := right j t k.val
    have hl' : 0 < (l : ℝ) := by exact_mod_cast hl
    have hlr' : (l : ℝ) < (r : ℝ) := by exact_mod_cast hlr
    have hr' : (r : ℝ) < 1 := by exact_mod_cast hr
    have hcell := preimage j t k h2 h5
    have hdom : Ioo (a0 (originalW2At j)) (singletonTop (originalW2At j) t) ⊆ singletonAmbient := by
      have hg := originalRepairedW2Bank_geometry _ (originalW2At_mem j)
      fin_cases t
      · exact W2Singleton2_subset hg
      · exact W2Singleton3_subset hg
      · exact W2Singleton4_subset hg
    have hsub : Ioo (l : ℝ) (r : ℝ) ⊆ singletonAmbient := by
      rw [← hcell]
      exact fun x hx => hdom hx.1
    have h1 : (1 : ℚ) ≤ r/l := (one_le_div (show 0 < l from hl)).2 hlr.le
    have h2log : (1 : ℚ) ≤ (1-l)/(1-r) :=
      (one_le_div (sub_pos.mpr (show r < 1 from hr))).2 (sub_le_sub_left hlr.le 1)
    have hL := series_lower h1
    have hR := series_lower h2log
    unfold singletonIntegralAtom
    rw [hcell]
    change _ ≤ singletonMass (Ioo (l : ℝ) (r : ℝ))
    rw [singletonMass_eq_original measurableSet_Ioo hsub, primitive hl' hlr'.le hr']
    push_cast at hL hR ⊢
    exact add_le_add hL hR
  · push_cast
    exact MeasureTheory.integral_nonneg_of_ae (Filter.Eventually.of_forall singletonKernel_nonneg)

/-- Directed lower comparison for each actual W2 lower-table cell,
with the three physical singleton measures and the outer W2 fifth. -/
theorem archive_weight_le_singletons (j : Fin 36) (k : Fin 200) :
    (archiveWeight j k.val : ℝ)/(2^80 : ℝ)/5 ≤ dynamicIdeal (.inr j) (.inr (.inl k)) := by
  have hc := List.all_eq_true.mp (original_checks j).1 k.val (List.mem_range.mpr k.isLt)
  have hw : (archiveWeight j k.val : ℚ)/(2^80 : ℚ) ≤ ∑ t : Fin 3, laneLower j t k.val :=
    of_decide_eq_true hc
  have hwr : (archiveWeight j k.val : ℝ)/(2^80 : ℝ) ≤ ∑ t : Fin 3, (laneLower j t k.val : ℝ) := by
    exact_mod_cast hw
  exact div_le_div_of_nonneg_right
    (hwr.trans (Finset.sum_le_sum (fun t _ => lane_le j t k))) (by norm_num)

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


/-- Original list mass after removing the per-product Q80 floors. Upper
selects the four genuine pair lists, lower the three singleton lists. -/
def archivedChannel (old : Table) (j : Fin 36) (upper : Bool) : ℝ :=
  let row := rows (slotOfAction (.inr j))
  let xs := if upper then row.upperWeights else row.lowerWeights
  (((xs.map (fun w => read old upper w.1 * w.2)).sum : ℤ) : ℝ) /
    (2^80 : ℝ) / 5 / (2^80 : ℝ)

theorem archived_w2_split (old : Table) (j : Fin 36) :
    idealFeedbackValue old (.inr j) = archivedChannel old j false + archivedChannel old j true := by
  have hd := (original_checks j).2.1
  unfold idealFeedbackValue unroundedNumerator literalFeedbackProducts
  rw [List.sum_append, Int.cast_add, hd]
  have hQ : (P2Selected430LiteralActionData.q : ℝ) = (2^80 : ℝ) := by
    norm_num [P2Selected430LiteralActionData.q]
  change (_ + _) / (P2Selected430LiteralActionData.q : ℝ) / (5 : ℝ) / (2^80 : ℝ) = _
  rw [hQ]
  unfold archivedChannel
  dsimp only
  ring

private theorem archive_lower_cells (old : Table) (j : Fin 36) :
    archivedChannel old j false = ∑ k : Fin 200,
      ((archiveWeight j k.val : ℝ)/(2^80 : ℝ)/5) * floorValue (old false) k := by
  unfold archivedChannel
  dsimp only
  rw [weighted_list, Int.cast_sum]
  simp_rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k _
  unfold archiveWeight floorValue
  rw [Int.cast_mul]
  ring

/-- The actual immutable 430 predecessor h covers the unrounded original
W2 singleton channel. Nonnegative knot weights and adjacent minima are
included in the true lower-atom sum. -/
theorem immutable_w2_singletons_le_integral (j : Fin 36) (g : Fin 430) :
    archivedChannel (iterate g.val) j false ≤
      ∑ b : FloorAtom, dynamicIdeal (.inr j) (.inr b) * floorAtomValue (precedingh g) b := by
  have hp (k : Fin 200) : 0 ≤ floorValue (precedingh g) k := by
    unfold floorValue
    exact div_nonneg (by exact_mod_cast iterate_nonneg g.val false k) (by positivity)
  have hkp (k : Fin 201) : 0 ≤ floorKnotValue (precedingh g) k := by
    unfold floorKnotValue
    split_ifs <;> first | exact hp _ | exact le_min (hp _) (hp _)
  rw [archive_lower_cells]
  calc
    _ ≤ ∑ k : Fin 200, dynamicIdeal (.inr j) (.inr (.inl k)) * floorValue (precedingh g) k :=
      Finset.sum_le_sum (fun k _ => mul_le_mul_of_nonneg_right
        (archive_weight_le_singletons j k) (hp k))
    _ ≤ _ := by
      rw [Fintype.sum_sum_type]
      apply le_add_of_nonneg_right
      apply Finset.sum_nonneg
      intro k _
      apply mul_nonneg _ (hkp k)
      exact div_nonneg (Finset.sum_nonneg (fun t _ =>
        MeasureTheory.integral_nonneg_of_ae (Filter.Eventually.of_forall singletonKernel_nonneg))) (by norm_num)

/-- Names the actual continuous good-pair contribution of all four Gamma
domains, still integrated against the true old upper-table lookup. -/
def integralPairs (j : Fin 36) (g : Fin 430) : ℝ :=
  ∑ b : FloorAtom, dynamicIdeal (.inr j) (.inl b) * floorAtomValue (precedingH g) b

/-- Only the genuine upper good-pair archive comparison remains among
the W2 variable feedback channels after the three lower channels are paid. -/
theorem immutable_w2_feedback_le_integral_plus_pairs (j : Fin 36) (g : Fin 430) :
    idealFeedbackValue (iterate g.val) (.inr j) ≤
      (∑ b : RowAtom, dynamicIdeal (.inr j) b * oldAtomValue (precedingH g) (precedingh g) b) +
        (archivedChannel (iterate g.val) j true - integralPairs j g) := by
  rw [archived_w2_split, Fintype.sum_sum_type]
  have h := immutable_w2_singletons_le_integral j g
  unfold integralPairs
  simp only [oldAtomValue]
  linarith only [h]

/-- Original upper pair coefficients compared in the same units as the
already-paid three lower channels. W1 has no variable upper channel. -/
def bankPairArchive (g : Fin 430) : Original106Action → ℝ
  | .inl _ => 0
  | .inr j => archivedChannel (iterate g.val) j true

def bankPairIntegral (g : Fin 430) : Original106Action → ℝ
  | .inl _ => 0
  | .inr j => integralPairs j g

private theorem feedback_with_pairs (g : Fin 430) (a : Original106Action) :
    fixedValue (iterate g.val true) a + idealFeedbackValue (iterate g.val) a ≤
      idealCellProfile (precedingH g) (precedingh g) a +
        (bankPairArchive g a - bankPairIntegral g a) := by
  have h : idealFeedbackValue (iterate g.val) a ≤
      (∑ b : RowAtom, dynamicIdeal a b * oldAtomValue (precedingH g) (precedingh g) b) +
        (bankPairArchive g a - bankPairIntegral g a) := by
    rcases a with ⟨i,j⟩ | j
    · simpa only [bankPairArchive, bankPairIntegral, sub_self, add_zero] using
        Part5OriginalH430W1ArchivedFeedback.immutable_w1_feedback_le_integral i j g
    · exact immutable_w2_feedback_le_integral_plus_pairs j g
  unfold idealCellProfile
  simp_rw [cellReadIdeal_split, add_mul]
  rw [Finset.sum_add_distrib, readFixed_value, one_mul]
  linarith only [h]

private theorem action_gap_after_singletons (N n : ℕ) (k : Root) (t : ℝ) (p : ℕ)
    (g : Fin 430) (a : Original106Action) (hN : 4 ≤ N) (ht : 0 ≤ t) (ht' : t ≤ 1/12)
    (hn : 1 / ((n : ℝ)+1) ≤ 11/384) (hp : p.Prime ∧ p.Coprime N)
    (hb : P2EnhancedLowerPrimeChildCarriers.physicalPrime N p ∈ rootBand k) :
    (∑ l ∈ selectedLevel N n k t p g a, levelDefect N n k t p g l +
      occurrenceScale N n k t p g l * feedbackRoundingLoss (iterate g.val) a) ≤
    (∑ l ∈ selectedLevel N n k t p g a, occurrenceScale N n k t p g l *
        (baseValue a + (bankPairArchive g a - bankPairIntegral g a))) +
      levelAppliedError N n k t p g a := by
  unfold levelAppliedError
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro l hl
  have h := bank_level_defect_le_candidate N n k t p g a hN ht ht' hn hp hb l hl
  have hscale := occurrenceScale_nonneg N n k t p g l hN ht ht' hn hp hb
  have hf := mul_le_mul_of_nonneg_left (feedback_with_pairs g a) hscale
  let F := idealCellProfile (precedingH g) (precedingh g) a
  let θ := occurrenceTheta N n k t p g l
  let child := childTerm N n k t p g l
  have habs : θ*F-child ≤ |child-θ*F| := by
    rw [abs_sub_comm]
    exact le_abs_self _
  have hm := mul_le_mul_of_nonneg_left habs (mark_pos (levelOccurrence l)).le
  calc
    _ ≤ bankCandidateGap N n k t p g a l +
          occurrenceScale N n k t p g l * feedbackRoundingLoss (iterate g.val) a :=
      add_le_add_right h _
    _ = occurrenceScale N n k t p g l * baseValue a +
          occurrenceScale N n k t p g l *
            (fixedValue (iterate g.val true) a + idealFeedbackValue (iterate g.val) a) -
          levelMark l * child := by
      rw [ideal_feedback_exact (iterate g.val) a]
      unfold bankCandidateGap occurrenceScale occurrenceTheta
      dsimp only [child]
      ring
    _ ≤ occurrenceScale N n k t p g l * (baseValue a + (bankPairArchive g a - bankPairIntegral g a)) +
          (occurrenceScale N n k t p g l * F - levelMark l * child) := by
      dsimp only [F]
      linarith only [hf]
    _ ≤ _ := by
      change _ ≤ occurrenceScale N n k t p g l * _ + levelMark l * |child-θ*F|
      apply add_le_add_left
      change levelMark l * θ * F - levelMark l * child ≤ levelMark l * |child-θ*F|
      change levelMark l * (θ*F-child) ≤ levelMark l * |child-θ*F| at hm
      linarith only [hm]

/-- The actual corrected 106-action bank needs its ordinary/switched
base and the four upper good-pair channels. Every archived W1 and W2
lower-singleton coefficient is paid. There is one existing error charge
at each action's own selected Theta, including its zero-mass branch. -/
theorem uniform_corrected_bank_after_singletons {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
    ∀ (n : ℕ) (k : Root) (t : ℝ) (p : ℕ) (g : Fin 430),
      0 ≤ t → t ≤ 1/12 → 1/((n : ℝ)+1) ≤ 11/384 →
      (p.Prime ∧ p.Coprime N) → P2EnhancedLowerPrimeChildCarriers.physicalPrime N p ∈ rootBand k →
      actualBankSourceGap N n k t p g +
        (∑ a : Original106Action, correctionOn N n k t p g (selectedLevel N n k t p g a)) +
        selectedBankRoundingLoss N n k t p g ≤
      (∑ a : Original106Action, ∑ l ∈ selectedLevel N n k t p g a,
          occurrenceScale N n k t p g l * (baseValue a + (bankPairArchive g a - bankPairIntegral g a))) +
        ε * actualBankTheta N n k t p g := by
  obtain ⟨T,hT4,hT⟩ := uniform_level_bank_supply hε
  refine ⟨T,hT4,?_⟩
  intro N hNT n k t p g ht ht' hn hp hb
  rw [corrected_bank_gap_eq_defects, selectedBankRoundingLoss]
  calc
    _ = ∑ a : Original106Action, ∑ l ∈ selectedLevel N n k t p g a,
          (levelDefect N n k t p g l +
            occurrenceScale N n k t p g l * feedbackRoundingLoss (iterate g.val) a) := by
      simp only [Finset.sum_add_distrib]
    _ ≤ ∑ a : Original106Action,
        ((∑ l ∈ selectedLevel N n k t p g a, occurrenceScale N n k t p g l *
            (baseValue a + (bankPairArchive g a - bankPairIntegral g a))) +
          ε * levelTheta N n k t p g a) := by
      apply Finset.sum_le_sum
      intro a _
      exact (action_gap_after_singletons N n k t p g a (hT4.trans hNT) ht ht' hn hp hb).trans
        (add_le_add_left (hT N hNT n k t ht ht' hn p hp hb g a).2.1 _)
    _ = _ := by simp only [actualBankTheta, Finset.sum_add_distrib, Finset.mul_sum]

end
end ImbalancedChen.Part5OriginalH430W2ArchivedSingletons

