import ImbalancedChen.P2HistoricalNativePointCounts

/-! The short sector only changes across boundaries of actual write prefixes,
the last positive seed cell, and the end of the common Buchstab clamp. No
evaluation of a point price, upper/lower entry, or winning action is used. -/
namespace ImbalancedChen.P2HistoricalLowTargetEdges

noncomputable section
open P2TableActionSourceOnly P2SimultaneousTableSourceOnly
open P2HistoricalLowerBankAncestry P2Historical248Authentication
open P2HistoricalScheduledPointReads P2HistoricalNativePointCounts
open Wu2008DoubleSieve

/-- Original W1/W2 rightmost target indices. The seed ends at 59 and the
constant upper Buchstab clamp at 99; both are already in the list. This
is a sufficient test set, not an assertion that all of its rows win. -/
def edges : List ℕ :=
  [50,51,52,53,54,55,56,57,59,61,63,64,65,67,69,71,73,74,75,77,
   79,81,83,84,85,87,89,94,99]

theorem edges_length : edges.length = 29 := rfl
private theorem seed_edge : 59 ∈ edges := by decide
private theorem clamp_edge : 99 ∈ edges := by decide

def stopAt (ts : List (Fin 200)) : ℕ := ((ts.map Fin.val).getLast?).getD 0
def aligned (ts : List (Fin 200)) : Bool :=
  decide (ts.map Fin.val = List.range (stopAt ts+1) ∧ stopAt ts ∈ edges)

/-- Three original parameter banks, target column only. The earlier
recalibrations alter only the base. No old or new h/H data is consulted. -/
private theorem original_prefixes :
    w1Original.all (fun a => aligned a.targets) = true ∧
    w2Original.all (fun a => aligned a.targets) = true ∧
    w2Added.all (fun a => aligned a.targets) = true := by decide

private theorem scheduled_w1 (n : ℕ) {a : W1Action} (ha : a ∈ designatedW1 n) :
    aligned a.targets = true := by
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp ha
  unfold sourceW1Schedule at hv
  split at hv
  · exact List.all_eq_true.mp original_prefixes.1 v hv
  · obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hv
    exact List.all_eq_true.mp original_prefixes.1 b.1 (List.of_mem_zip hb).1

private theorem updated_w2 (us : List P2HistoricalSourceJSON.Value)
    {a : W2Action} (ha : a ∈ (w2Original.zip us).map
      (fun p => { p.1 with base := P2HistoricalSourceJSON.integer
        (P2HistoricalSourceJSON.field p.2 "new_base") })) : aligned a.targets = true := by
  obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ha
  exact List.all_eq_true.mp original_prefixes.2.1 b.1 (List.of_mem_zip hb).1

private theorem scheduled_w2 (n : ℕ) {a : W2Action} (ha : a ∈ designatedW2 n) :
    aligned a.targets = true := by
  unfold designatedW2 sourceW2Schedule at ha
  split_ifs at ha
  · simp at ha
  · exact List.all_eq_true.mp original_prefixes.2.1 a ha
  · exact updated_w2 _ ha
  · exact updated_w2 _ ha
  · rcases List.mem_append.mp ha with h | h
    · exact updated_w2 _ h
    · exact List.all_eq_true.mp original_prefixes.2.2 a h

private theorem moves_right {ts : List (Fin 200)} (ht : aligned ts = true)
    {i j : Fin 200} (hij : j.val=i.val+1) (hi : i.val ∉ edges) (hm : i ∈ ts) : j ∈ ts := by
  have hh : ts.map Fin.val = List.range (stopAt ts+1) ∧ stopAt ts ∈ edges := of_decide_eq_true ht
  have hin : i.val ∈ ts.map Fin.val := List.mem_map.mpr ⟨i,hm,rfl⟩
  rw [hh.1] at hin
  have hle := List.mem_range.mp hin
  have hne : i.val ≠ stopAt ts := fun h => hi (by simpa only [h] using hh.2)
  have hj : j.val ∈ ts.map Fin.val := by rw [hh.1]; exact List.mem_range.mpr (by omega)
  obtain ⟨v,hv,he⟩ := List.mem_map.mp hj
  exact (Fin.ext he : v = j) ▸ hv

private theorem w1_order (old cur : Table) (xs : List W1Action) (i j : Fin 200)
    (hcur : cur true i ≤ cur true j) (hij : ∀ a ∈ xs, i ∈ a.targets → j ∈ a.targets) :
    applyW1Bank old cur xs true i ≤ applyW1Bank old cur xs true j := by
  induction xs generalizing cur with
  | nil => exact hcur
  | cons a xs ih =>
    change applyW1Bank old _ xs true i ≤ applyW1Bank old _ xs true j
    apply ih _ _ (fun b hb => hij b (List.mem_cons_of_mem a hb))
    by_cases hi : i ∈ a.targets
    · have hj := hij a (by simp) hi
      simpa [P2OriginalW1CandidateIntegerABI.apply,hi,hj] using
        max_le_max hcur (le_refl (P2OriginalW1CandidateIntegerABI.candidate old a))
    · have he : P2OriginalW1CandidateIntegerABI.apply old cur a true i = cur true i := by
        simp [P2OriginalW1CandidateIntegerABI.apply,hi]
      rw [he]
      exact hcur.trans (P2OriginalW1CandidateIntegerABI.apply_retains old cur a true j)

private theorem w2_order (old cur : Table) (xs : List W2Action) (i j : Fin 200)
    (hcur : cur true i ≤ cur true j) (hij : ∀ a ∈ xs, i ∈ a.targets → j ∈ a.targets) :
    applyW2Bank old cur xs true i ≤ applyW2Bank old cur xs true j := by
  induction xs generalizing cur with
  | nil => exact hcur
  | cons a xs ih =>
    change applyW2Bank old _ xs true i ≤ applyW2Bank old _ xs true j
    apply ih _ _ (fun b hb => hij b (List.mem_cons_of_mem a hb))
    by_cases hi : i ∈ a.targets
    · have hj := hij a (by simp) hi
      simpa [P2OriginalW2CandidateIntegerABI.apply,hi,hj] using
        max_le_max hcur (le_refl (P2OriginalW2CandidateIntegerABI.candidate old a))
    · have he : P2OriginalW2CandidateIntegerABI.apply old cur a true i = cur true i := by
        simp [P2OriginalW2CandidateIntegerABI.apply,hi]
      rw [he]
      exact hcur.trans (P2OriginalW2CandidateIntegerABI.apply_retains old cur a true j)

private theorem buchstab_order (old : Table) (i j : Fin 200) (hj : j.val<100)
    (hij : j.val=i.val+1) (hcur : old true i ≤ old true j) :
    buchstabStep old true i ≤ buchstabStep old true j := by
  by_cases h50 : 50 ≤ i.val
  · have h50' : 50 ≤ j.val := by omega
    have ki : max 50 (i.val-49) = 50 := by omega
    have kj : max 50 (j.val-49) = 50 := by omega
    simpa [buchstabStep,h50,h50',ki,kj] using max_le_max hcur
      (le_refl (suffixNumerator P2HistoricalBankLogWeights.historicalLogWeights old false 50))
  · have hr : old true j ≤ buchstabStep old true j := by
      unfold buchstabStep
      split_ifs <;> first | exact le_max_left _ _ | exact le_rfl
    simpa [buchstabStep,h50] using hcur.trans hr

/-- In the real historical table one step to the right costs no larger
licence between successive breakpoints. At the left-of-2 guard this is a
one-sided inequality, not a fictitious entrywise equality. -/
theorem below_next_at_unbroken (n : ℕ) (i j : Fin 200) (hj : j.val<100)
    (hij : j.val=i.val+1) (hi : i.val ∉ edges) : outputAt n true i ≤ outputAt n true j := by
  induction n with
  | zero =>
    have h59 : i.val ≠ 59 := fun h => hi (by simpa only [h] using seed_edge)
    by_cases h : i.val<60
    · have h' : j.val<60 := by omega
      simp [outputAt,iterate,originalSeed,h,h']
    · have h' : ¬j.val<60 := by omega
      simp [outputAt,iterate,originalSeed,h,h']
  | succ n ih =>
    change oneRound (outputAt n) (designatedW1 n) (designatedW2 n) true i ≤
      oneRound (outputAt n) (designatedW1 n) (designatedW2 n) true j
    unfold oneRound
    apply w2_order _ _ _ _ _ _ (fun a ha => moves_right (scheduled_w2 n ha) hij hi)
    apply w1_order _ _ _ _ _ _ (fun a ha => moves_right (scheduled_w1 n ha) hij hi)
    exact buchstab_order _ i j hj hij ih

theorem low_of_edges (n : ℕ) {δ : ℝ} (hd : 0<δ) (hd' : δ≤1/10)
    (he : ∀ i : Fin 200, i.val ∈ edges → readGain n i ≤ H δ (tableGrid (i.val+1))) :
    ∀ i : Fin 200, i.val<100 → readGain n i ≤ H δ (tableGrid (i.val+1)) := by
  have aux (d : ℕ) : ∀ i : Fin 200, i.val < 100 → 99-i.val=d →
      readGain n i ≤ H δ (tableGrid (i.val+1)) := by
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro i hi hid
      by_cases hm : i.val ∈ edges
      · exact he i hm
      have hne : i.val ≠ 99 := fun h => hm (by simpa only [h] using clamp_edge)
      let j : Fin 200 := ⟨i.val+1,by omega⟩
      have hj : j.val < 100 := by dsimp [j]; omega
      have hstep := below_next_at_unbroken n i j hj rfl hm
      have hr : (outputAt n true i : ℝ) ≤ outputAt n true j := by exact_mod_cast hstep
      have hs : readGain n i ≤ readGain n j :=
        div_le_div_of_nonneg_right hr (Nat.cast_nonneg tableQ)
      have hnext := ih (99-j.val) (by dsimp [j]; omega) j hj rfl
      have hiB := tableGrid_bounds (show i.val+1≤200 by omega)
      have hjB := tableGrid_bounds (show j.val+1≤200 by omega)
      have hmono := wuImprovementLimit_upper_antitone hd hd'
        ⟨hiB.1,hiB.2.trans (by norm_num)⟩ ⟨hjB.1,hjB.2.trans (by norm_num)⟩
        (tableGrid_mono (show i.val+1 ≤ j.val+1 by dsimp [j]; omega))
      exact hs.trans (hnext.trans hmono)
  exact fun i hi => aux _ i hi rfl

/-- Only 29 explicit low H247 comparisons are sufficient for the original
consumer. The 29 analytic estimates remain to be proved. -/
theorem original_bank_from_edges {δ : ℝ} (hd : 0<δ) (hd' : δ≤1/10)
    (he : ∀ i : Fin 200, i.val ∈ edges → readGain 247 i ≤ H δ (tableGrid (i.val+1))) :
    P2HistoricSavedOrdinaryDefectAssembly.BankEndpointLicences δ :=
  actual_bank_from_low_upper hd hd' (low_of_edges 247 hd hd' he)

theorem original_native_point_prices_from_edges (n k : ℕ) {δ ε : ℝ}
    (hd : 0<δ) (hd' : δ≤1/10) (hε : 0<ε)
    (he : ∀ i : Fin 200, i.val ∈ edges → readGain n i ≤ H δ (tableGrid (i.val+1))) :
    PointPrices (n+2) k δ ε :=
  later_point_prices n k hd hd' hε (low_of_edges n hd hd' he)

end
end ImbalancedChen.P2HistoricalLowTargetEdges
