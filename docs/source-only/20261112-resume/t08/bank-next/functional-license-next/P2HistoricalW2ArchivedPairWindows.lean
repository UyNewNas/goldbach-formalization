import ImbalancedChen.P2HistoricalW2NativeFunctional
import ImbalancedChen.Part5OriginalH430W2UpperBankPayment

/-! The coefficient theorem used here has no generation or occurrence
state. Match its four ordered lists to the actual H248 record, then
evaluate the original per-product floors on its own preceding array. -/
namespace ImbalancedChen.P2HistoricalW2ArchivedPairWindows

noncomputable section
open Set Filter MeasureTheory
open scoped BigOperators Topology
open P2HistoricalSourceJSON P2Historical248Authentication P2HistoricalScheduledPointReads
open P2HistoricalNativePointCounts P2HistoricalLowerBankAncestry P2TableActionSourceOnly
open P5OriginalActionMassBound P5OriginalFeedbackDomains P5OriginalFeedbackTableKernels
open Part5OriginalUpsilon5CausalDictionary Part5OriginalH430LiteralBankBudget
open P2OriginalBankOldProfilePassage P2OriginalPhysicalOldProfileMass P2OriginalHalfOpenProfileCarrier
open P2OriginalChildPhysicalNormalization P2OriginalW2CountTupleReindex
open Part5OriginalH430W2UpperArchiveData (weights)
open Part5OriginalH430W2UpperPolygons (parameterQ)
open Part5OriginalH430W2UpperWeights (weightAt)

abbrev W := P2OriginalW2CandidateIntegerABI.WeightRow
def encode (xs : List W) : List (ℕ × ℤ) := xs.map (fun r => (r.index.val,r.lower))
def lane (a : W2Action) (k : Fin 4) : List W := (a.pairRows[k.val]?).getD []
private def matches (v : Value) (j : Fin 36) : Bool :=
  decide (parameters v=List.ofFn (parameterQ j) ∧ (readW2 v).pairRows.length=4) &&
    (List.finRange 4).all (fun k => decide (encode (lane (readW2 v) k)=weights j k))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- Only literal tuple and ordered index/numerator identities. -/
private theorem raw_matches :
    (oldRows++addedRows).all (fun v => (List.finRange 36).any (matches v))=true := by decide

private theorem priced_pairs {vs us : List Value} {b : Tagged} (hb : b∈reprice vs us) :
    b.2.pairRows=(readW2 b.1).pairRows := by
  induction vs generalizing us with
  | nil => simp [reprice] at hb
  | cons v vs ih =>
    cases us with
    | nil => simp [reprice] at hb
    | cons u us =>
      change b ∈ _ :: reprice vs us at hb
      rcases List.mem_cons.mp hb with rfl | hh
      · rfl
      · exact ih hh

private theorem tagged_pairs {vs : List Value} {b : Tagged} (hb : b∈tag vs) :
    b.2.pairRows=(readW2 b.1).pairRows := by
  obtain ⟨v,_,rfl⟩ := List.mem_map.mp hb
  rfl

private theorem scheduled_pairs (g : ℕ) {b : Tagged} (hb : b∈taggedW2 g) :
    b.2.pairRows=(readW2 b.1).pairRows := by
  unfold taggedW2 at hb
  split_ifs at hb
  · simp at hb
  · exact tagged_pairs hb
  · exact priced_pairs hb
  · exact priced_pairs hb
  · exact (List.mem_append.mp hb).elim priced_pairs tagged_pairs

theorem actual_pair_lists (g : ℕ) {b : Tagged} (hb : b∈taggedW2 g) :
    ∃ j : Fin 36, parameters b.1=List.ofFn (parameterQ j) ∧ b.2.pairRows.length=4 ∧
      ∀ k : Fin 4, encode (lane b.2 k)=weights j k := by
  obtain ⟨j,_,hj⟩ := List.any_eq_true.mp
    (List.all_eq_true.mp raw_matches b.1 (P2HistoricalW2NativeFunctional.original_parameters g hb))
  obtain ⟨hc,hk⟩ := Bool.and_eq_true.mp hj
  obtain ⟨hp,hn⟩ := of_decide_eq_true hc
  have hr := scheduled_pairs g hb
  refine ⟨j,hp,by simpa only [hr] using hn,?_⟩
  intro k
  have hraw := of_decide_eq_true (List.all_eq_true.mp hk k (List.mem_finRange k))
  simpa only [lane,hr] using hraw

private theorem floor_numerator (old : Table) (xs : List W) :
    sourceWeightSum old true xs*(tableQ : ℤ) ≤
      ∑ i : Fin 200,old true i*weightAt (encode xs) i.val := by
  classical
  have one (r : W) : (∑ i : Fin 200,old true i*(if r.index.val=i.val then r.lower else 0)) =
      old true r.index*r.lower := by
    rw [Finset.sum_eq_single r.index]
    · simp
    · intro i _ hi
      have hne : r.index.val≠i.val := fun h => hi (Fin.ext h.symm)
      simp [hne]
    · simp
  induction xs with
  | nil => simp [sourceWeightSum,encode,weightAt]
  | cons r xs ih =>
    have split (i : Fin 200) : weightAt (encode (r::xs)) i.val =
        (if r.index.val=i.val then r.lower else 0)+weightAt (encode xs) i.val := by
      simp [encode,weightAt]
    simp_rw [split,mul_add]
    rw [Finset.sum_add_distrib,one]
    change (old true r.index*r.lower/(tableQ : ℤ)+sourceWeightSum old true xs)*(tableQ : ℤ) ≤ _
    rw [add_mul]
    exact add_le_add (Int.ediv_mul_le _ (show (tableQ : ℤ)≠0 by exact_mod_cast tableQ_pos.ne')) ih

private theorem rounded_le_cells (old : Table) (xs : List W) :
    (sourceWeightSum old true xs : ℝ)/tableQ ≤
      ∑ i : Fin 200,((weightAt (encode xs) i.val : ℝ)/(2^80 : ℝ))*floorValue (old true) i := by
  have hq : (0 : ℝ)<tableQ := by exact_mod_cast tableQ_pos
  have hc : (sourceWeightSum old true xs : ℝ)*(tableQ : ℝ) ≤
      ∑ i : Fin 200,(old true i : ℝ)*(weightAt (encode xs) i.val : ℝ) := by
    exact_mod_cast floor_numerator old xs
  have hid : (∑ i : Fin 200,(old true i : ℝ)*(weightAt (encode xs) i.val : ℝ))/
        ((tableQ : ℝ)*(tableQ : ℝ)) =
      ∑ i : Fin 200,((weightAt (encode xs) i.val : ℝ)/(2^80 : ℝ))*floorValue (old true) i := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    rw [show (tableQ : ℝ)=(2^80 : ℝ) by norm_num [tableQ],floorValue]
    ring
  rw [←hid]
  apply (le_div_iff₀ (mul_pos hq hq)).mpr
  calc
    _ = (sourceWeightSum old true xs : ℝ)*(tableQ : ℝ) := by field_simp [hq.ne'] <;> ring
    _ ≤ _ := hc

/-- All four archived lanes, preserving each separate product floor,
are paid by the actual old array's four original legal pair integrals.
The H used on every open cell and every knot is outputAt g. -/
theorem historical_pair_integrals (g : ℕ) {b : Tagged} (hb : b∈taggedW2 g) :
    ∃ j : Fin 36, parameters b.1=List.ofFn (parameterQ j) ∧ b.2.pairRows.length=4 ∧
      ∀ k : Fin 4, (sourceWeightSum (outputAt g) true (lane b.2 k) : ℝ)/tableQ ≤
        pairOldIntegral (originalW2At j) k (outputAt g true) := by
  obtain ⟨j,hp,hn,hlist⟩ := actual_pair_lists g hb
  refine ⟨j,hp,hn,?_⟩
  intro k
  have hf (i : Fin 200) : 0≤floorValue (outputAt g true) i :=
    div_nonneg (by exact_mod_cast iterate_nonnegative designatedW1 designatedW2 g true i) (by positivity)
  have hk (i : Fin 201) : 0≤floorKnotValue (outputAt g true) i := by
    unfold floorKnotValue
    split_ifs <;> first | exact hf _ | exact le_min (hf _) (hf _)
  have hr := rounded_le_cells (outputAt g) (lane b.2 k)
  rw [hlist k] at hr
  rw [←pairIntegralAtom_value (originalRepairedW2Bank_geometry _ (originalW2At_mem j)),Fintype.sum_sum_type]
  apply hr.trans
  apply le_trans (Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right
    (Part5OriginalH430W2UpperBankPayment.all36_four_original_pair_measures j k i) (hf i)))
  apply le_add_of_nonneg_right
  exact Finset.sum_nonneg (fun i _ => mul_nonneg
    (MeasureTheory.integral_nonneg_of_ae (Filter.Eventually.of_forall pairKernel_nonneg)) (hk i))

def physicalWindow (N : ℕ) (Q L : ℝ) (d : ℕ) (j : Fin 36) (k : Fin 4) (g : ℕ) : ℝ :=
  windowOccurrence N Q L d (originalW2At j) k fun p r =>
    (localPrimeFactor d p*localPrimeFactor (d*p) r)*
      pairTest (originalW2At j) k (outputAt g true) (normalizedLog N L ![p,r])

private theorem window_eq {N d : ℕ} {Q L : ℝ} (hN : 1<N) (hd : 0<d) (hL : 0<L)
    (hQ : Q=(d:ℝ)*(N:ℝ)^L) (j : Fin 36) (k : Fin 4) (g : ℕ) :
    physicalWindow N Q L d j k g=truePairOldProfile N L d (originalW2At j) k (outputAt g true) := by
  unfold physicalWindow
  rw [all_four_window_occurrences_reindex hN hd hL hQ
    (originalRepairedW2Bank_geometry _ (originalW2At_mem j))]
  unfold truePairOldProfile truePairTest
  apply Finset.sum_congr rfl
  intro x _
  have hh : (![x 0,x 1] : Fin 2 → ℕ)=x := by
    funext i
    fin_cases i <;> rfl
  by_cases hx : normalizedLog N L x∈pairHalf (originalW2At j) k
  · simp only [if_pos hx,indicator_of_mem hx,hh]
  · simp only [if_neg hx,indicator_of_notMem hx,mul_zero]

/-- One threshold before all 248 immutable predecessors and all physical
prime pairs, retaining both old Euler factors and both insertion gates.
The four quantities here are the old-profile feedback before /5. -/
theorem historical_pair_windows {lo hi ε : ℝ} (hlo : 0<lo) (hhi : lo≤hi) (he : 0<ε) :
    ∃ T : ℕ, 2≤T ∧ ∀ (g : Fin 248) (b : Tagged), b∈taggedW2 g.val →
      ∃ j : Fin 36, parameters b.1=List.ofFn (parameterQ j) ∧ b.2.pairRows.length=4 ∧
        ∀ N, T≤N → ∀ L∈Icc lo hi, ∀ d : ℕ, 0<d → ∀ Q : ℝ, Q=(d:ℝ)*(N:ℝ)^L →
        ∀ k : Fin 4, (sourceWeightSum (outputAt g.val) true (lane b.2 k) : ℝ)/tableQ ≤
          physicalWindow N Q L d j k g.val+ε := by
  have hf (g : Fin 248) : ∀ᶠ N : ℕ in atTop, ∀ L∈Icc lo hi, ∀ d : ℕ,
      ∀ j : Fin 36, ∀ k : Fin 4,
      |truePairOldProfile N L d (originalW2At j) k (outputAt g.val true)-
        pairOldIntegral (originalW2At j) k (outputAt g.val true)|<ε := by
    obtain ⟨T,hT⟩ := all36_four_true_old_H_profiles hlo hhi he (outputAt g.val true)
    exact eventually_atTop.mpr ⟨T,hT⟩
  obtain ⟨T,hT⟩ := eventually_atTop.mp (eventually_all.mpr hf)
  refine ⟨max 2 T,le_max_left _ _,?_⟩
  intro g b hb
  obtain ⟨j,hp,hn,hr⟩ := historical_pair_integrals g.val hb
  refine ⟨j,hp,hn,?_⟩
  intro N hN L hL d hd Q hQ k
  have hh := (abs_lt.mp (hT N ((le_max_right _ _).trans hN) g L hL d j k)).1
  rw [window_eq (by omega) hd (hlo.trans_le hL.1) hQ]
  linarith only [hr k, hh]

end
end ImbalancedChen.P2HistoricalW2ArchivedPairWindows
