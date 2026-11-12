import ImbalancedChen.P2HistoricalLowerBankAncestry

/-!
Upper cells strictly to the right of 3 cannot be written by the original
W1/W2 prefix targets.  On those cells the retained maximum is exactly the
latest lower-to-upper Buchstab suffix. This is a statement about the historical
integer iteration, with its existing rounded log weights. The second step
uses the native Wu upper cross inequality; no numerical result is evaluated.
-/

namespace ImbalancedChen.P2HistoricalHighPointAncestry

noncomputable section
open P2TableActionSourceOnly P2SimultaneousTableSourceOnly
open P2HistoricalBankLogWeights P2HistoricalLowerBankAncestry
open Wu2008DoubleSieve
open scoped BigOperators Interval

variable (w₁ : ℕ → List W1Action) (w₂ : ℕ → List W2Action)

/-- Pure support condition on the *output targets*; it asserts no estimate. -/
def LowWrites : Prop :=
  (∀ n, ∀ a ∈ w₁ n, ∀ i ∈ a.targets, i.val < 100) ∧
  (∀ n, ∀ a ∈ w₂ n, ∀ i ∈ a.targets, i.val < 100)

private theorem w1_skip (old cur : Table) (xs : List W1Action) (i : Fin 200)
    (hx : ∀ a ∈ xs, i ∉ a.targets) :
    applyW1Bank old cur xs true i = cur true i := by
  induction xs generalizing cur with
  | nil => rfl
  | cons a xs ih =>
    have ha := hx a (by simp)
    rw [applyW1Bank, ih _ (fun b hb => hx b (by simp [hb]))]
    simp [P2OriginalW1CandidateIntegerABI.apply, ha]

private theorem w2_skip (old cur : Table) (xs : List W2Action) (i : Fin 200)
    (hx : ∀ a ∈ xs, i ∉ a.targets) :
    applyW2Bank old cur xs true i = cur true i := by
  induction xs generalizing cur with
  | nil => rfl
  | cons a xs ih =>
    have ha := hx a (by simp)
    rw [applyW2Bank, ih _ (fun b hb => hx b (by simp [hb]))]
    simp [P2OriginalW2CandidateIntegerABI.apply, ha]

private theorem upper_round (hw : LowWrites w₁ w₂) (n : ℕ) (old : Table)
    (i : Fin 200) (hi : 100 ≤ i.val) :
    oneRound old (w₁ n) (w₂ n) true i =
      max (old true i) (suffixNumerator historicalLogWeights old false (max 50 (i.val-49))) := by
  rw [oneRound, w2_skip _ _ _ _ (fun a ha him => (not_lt_of_ge hi) (hw.2 n a ha i him)),
    w1_skip _ _ _ _ (fun a ha him => (not_lt_of_ge hi) (hw.1 n a ha i him))]
  simp [buchstabStep, show 50 ≤ i.val by omega]

/-- No contribution from a W1/W2 write or the positive seed at this
index. In particular, this does not charge the maximum as a sum. -/
theorem high_last_suffix (hw : LowWrites w₁ w₂) (n : ℕ) (i : Fin 200)
    (hi : 100 ≤ i.val) :
    iterate w₁ w₂ (n+1) true i =
      suffixNumerator historicalLogWeights (iterate w₁ w₂ n) false (max 50 (i.val-49)) := by
  induction n with
  | zero =>
    rw [iterate, upper_round w₁ w₂ hw 0 _ i hi]
    have hz : originalSeed true i = 0 := by simp [originalSeed, show ¬i.val < 60 by omega]
    change max (originalSeed true i) _ = _
    rw [hz]
    exact max_eq_right (suffix_nonnegative originalSeed_nonnegative false _)
  | succ n ih =>
    rw [iterate, upper_round w₁ w₂ hw (n+1) _ i hi, ih]
    exact max_eq_right (suffixNumerator_mono historicalLogWeights
      (iterate_retains w₁ w₂ n) false (by omega))

/-- Only the preceding lower side actually read by the suffix is needed.
The clamp is always above 2, even at the boundary. Unread input cells are
replaced by zero in the auxiliary majorization, never in the real history. -/
theorem high_endpoint_from_lower_tail {δ : ℝ} (hδ : 0<δ) (hδhi : δ≤1/10)
    (hw : LowWrites w₁ w₂) (n : ℕ) (i : Fin 200) (hi : 100 ≤ i.val)
    (hold : ∀ j : Fin 200, max 50 (i.val-49) ≤ j.val →
      (iterate w₁ w₂ n false j : ℝ)/tableQ ≤ h δ (tableGrid (j.val+1))) :
    (iterate w₁ w₂ (n+1) true i : ℝ)/tableQ ≤ H δ (tableGrid (i.val+1)) := by
  let k := max 50 (i.val-49)
  let v : ℕ → ℤ := fun j => if k ≤ j then read (iterate w₁ w₂ n) false j else 0
  have hk : k ≤ 200 := by dsimp [k]; omega
  have hnn : ∀ j < 200, 0 ≤ v j := by
    intro j hj
    dsimp [v]
    split_ifs
    · exact read_nonnegative (iterate_nonnegative w₁ w₂ n) false j
    · exact le_rfl
  have hlic : ∀ j < 200, (v j : ℝ)/tableQ ≤ wuImprovementLimit false δ (tableGrid (j+1)) := by
    intro j hj
    by_cases hkj : k ≤ j
    · simpa [v, hkj, read, hj, h] using hold ⟨j,hj⟩ hkj
    · have hb := tableGrid_bounds (show j+1 ≤ 200 by omega)
      simpa [v, hkj] using wuImprovementLimit_nonneg false hδ (by linarith : δ<1/2)
        hb.1 (hb.2.trans (by norm_num))
  have ht := rounded_original_grid_tail_sound false v logWeight hδ hδhi tableQ_pos hk
    (show (if false then 0 else 50 : ℕ) ≤ k from le_max_left _ _) hnn
    (fun j _ => logWeight_nonnegative j) hlic (fun j _ => logWeight_le_log j)
  have heq : (suffixNumerator historicalLogWeights (iterate w₁ w₂ n) false k : ℝ)/tableQ =
      ∑ j ∈ Finset.range (200-k), roundedProduct tableQ (v (k+j)) (logWeight (k+j)) := by
    rw [suffixNumerator_scaled]
    apply Finset.sum_congr rfl
    intro j _
    simp [v, historicalLogWeights, Nat.le_add_right]
  rw [← heq] at ht
  have hg : 50 ≤ i.val := by omega
  have hs := tableGrid_mono (show 50 ≤ i.val+1 by omega)
  have hs2 : 2 ≤ tableGrid (i.val+1) := by simpa [tableGrid] using hs
  have hs5 := (tableGrid_bounds (show i.val+1 ≤ 200 by omega)).2
  rw [high_last_suffix w₁ w₂ hw n i hi]
  change (suffixNumerator historicalLogWeights (iterate w₁ w₂ n) false k : ℝ)/tableQ ≤ _
  change _ ≤ ∫ u in tableGrid (max 50 (i.val-49))..5, h δ u / u at ht
  rw [tableGrid_upper_start hg] at ht
  exact ht.trans (buchstab_upper_integral_sound hδ hδhi hs2 hs5)

/-- Each upper anchor at generation n+2 uses h at n+1, which in turn
uses H at n. It does not need *any* assertion about the upper side at
n+1 or n+2. -/
theorem high_endpoint_two_generations {δ : ℝ} (hδ : 0<δ) (hδhi : δ≤1/10)
    (hw : LowWrites w₁ w₂) (n : ℕ)
    (hprev : UpperEndpoints δ (iterate w₁ w₂ n)) (i : Fin 200) (hi : 100 ≤ i.val) :
    (iterate w₁ w₂ (n+2) true i : ℝ)/tableQ ≤ H δ (tableGrid (i.val+1)) :=
  high_endpoint_from_lower_tail w₁ w₂ hδ hδhi hw (n+1) i hi
    (fun j _ => iterate_lower_endpoints hδ hδhi w₁ w₂ n hprev j)

private theorem below_of_le {n m : ℕ} (hnm : n ≤ m) :
    Below (iterate w₁ w₂ n) (iterate w₁ w₂ m) := by
  induction m, hnm using Nat.le_induction with
  | base => exact fun _ _ => le_rfl
  | succ m _ ih => exact fun u j => (ih u j).trans (iterate_retains w₁ w₂ m u j)

/-- Reduction for an entire finite history. A bound on the low upper
entries of its *last* table dominates earlier low entries by retention.
Both crossing directions, the initial high zero, and all high cells are
proved here; the remaining low upper estimates are explicitly unpaid. -/
theorem upper_endpoints_from_low {δ : ℝ} (hδ : 0<δ) (hδhi : δ≤1/10)
    (hw : LowWrites w₁ w₂) (m : ℕ)
    (low : ∀ i : Fin 200, i.val < 100 →
      (iterate w₁ w₂ m true i : ℝ)/tableQ ≤ H δ (tableGrid (i.val+1))) :
    ∀ n, n ≤ m → UpperEndpoints δ (iterate w₁ w₂ n) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn i
    by_cases hil : i.val < 100
    · have hc : (iterate w₁ w₂ n true i : ℝ) ≤ iterate w₁ w₂ m true i := by
        exact_mod_cast below_of_le w₁ w₂ hn true i
      exact (div_le_div_of_nonneg_right hc (Nat.cast_nonneg tableQ)).trans (low i hil)
    have hii : 100 ≤ i.val := by omega
    cases n with
    | zero =>
      have hb := tableGrid_bounds (show i.val+1 ≤ 200 by omega)
      simpa [iterate, originalSeed, show ¬i.val<60 by omega, H] using
        wuImprovementLimit_nonneg true hδ (by linarith : δ<1/2) hb.1 (hb.2.trans (by norm_num))
    | succ n =>
      cases n with
      | zero =>
        apply high_endpoint_from_lower_tail w₁ w₂ hδ hδhi hw 0 i hii
        intro j _
        have hb := tableGrid_bounds (show j.val+1 ≤ 200 by omega)
        simpa [iterate, originalSeed, h] using
          wuImprovementLimit_nonneg false hδ (by linarith : δ<1/2) hb.1 (hb.2.trans (by norm_num))
      | succ n =>
        exact high_endpoint_two_generations w₁ w₂ hδ hδhi hw n
          (ih n (by omega) (by omega)) i hii

end
end ImbalancedChen.P2HistoricalHighPointAncestry
