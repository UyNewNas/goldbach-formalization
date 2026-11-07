import ImbalancedChen.Part3ActualWFineKeyInitialization

/-!
# The actual W-close branch selects the first original fine slot

SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

The manuscript's close rescue uses the largest singleton. The literal
row-4 least-winner whole-cell theorem supplies theta+e/2 <= v(s0), not
merely a bound on W. Its three tent lines give an original first-slot
interval with lower reserve e and upper reserve e/3. Canonical fine keys
with sigma <= e/64 retain upper reserve e/4.

Original all-rank retained support and sigma*(k+1) <= e/2 pay the full
key vector. Removing its first occurrence then gives every complementary
key square by exact prefix cancellation. Thus the computed two-capacity
run on the same original remaining label word is legal whenever its
remaining capacity is at least one. The below-one full-vector repair,
same-rho small attachment and monomial consumer are separate obligations.
-/

namespace ImbalancedChen.Part3.ActualWCloseFineHead

noncomputable section

open ActualWFineWordAdapter ActualWThreeCapacityRun VariableEnvelope
open MathlibNt.SieveTheory.LiLiuPrereqWFBoxAllocation

/-- The true close decision licenses the first ORIGINAL slot on the whole
cell, including equality in the close/gap decision. -/
theorem actual_close_fine_head_bounds {e sigma : ℝ} {m N : ℕ}
    {j : ActualExtendedThirdDyadicLabel m}
    (he0 : 0 < e) (he : e ≤ 1 / 384) (hsigma : sigma ≤ e / 64)
    (hmesh : actualExtendedThirdDyadicStep m ≤ e / 32)
    (hfull : actualExtendedThirdDyadicHi m j 0 ≤ mu - 4 * e)
    {t : Fin 3 → ℝ} (ht : t ∈ actualExtendedThirdPhysicalCell m j)
    (hwinner : actualExtendedThirdLeastWinningIndex e m j = 4)
    (hclose : wInner (t 0) (t 1) (t 2) - v (t 0) ≤ e / 4)
    (hN : 1 < N) (p : Fin 3 → ℕ) (hp : ∀ i, 0 < p i)
    (hs : actualSelectedPrimeCoordinates (N : ℝ) p ∈ actualExtendedThirdPhysicalCell m j)
    (label : ℕ) (hlabel : p 0 ∈ actualPrimeFineLabelFinset N sigma label) :
    let theta := actualExtendedThirdBaseParameter e m j
    1 / 2 ≤ theta ∧ theta < 5 / 8 ∧
      actualExtendedThirdPhysicalLevel e m j + e ≤ theta ∧
      (N : ℝ) ^ (2 * theta - 1 + e) ≤ (actualPrimeFineLabelIntegerUpper N sigma label : ℝ) ∧
      (actualPrimeFineLabelIntegerUpper N sigma label : ℝ) ≤
        (N : ℝ) ^ (actualSelectedSubproductUpper 1 theta - e / 4) := by
  have hNr : (1 : ℝ) < N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := zero_lt_one.trans hNr
  rcases actualExtendedThirdSelectedRescue_wholeCell he0 he hmesh hfull ht false hwinner with
    ⟨_, hlo, hhi, hlevel, hcell⟩ | ⟨hgap, _⟩
  · let theta := actualExtendedThirdBaseParameter e m j
    have htent := hcell _ hs
    simp only [v, A, C, le_min_iff] at htent
    obtain ⟨hline0, hline1, hline2⟩ := htent
    have hloglower : 2 * theta - 1 + e ≤ actualSelectedPrimeCoordinates (N : ℝ) p 0 := by
      dsimp [theta]
      linarith
    have hlogupper : actualSelectedPrimeCoordinates (N : ℝ) p 0 + e / 3 ≤
        actualSelectedSubproductUpper 1 theta := by
      unfold actualSelectedSubproductUpper
      apply le_min <;> dsimp [theta] <;> linarith
    have hlower : (N : ℝ) ^ (2 * theta - 1 + e) ≤ (p 0 : ℝ) := by
      rw [← rpow_actualSelectedPrimeCoordinates (N : ℝ) hNr p hp 0]
      exact Real.rpow_le_rpow_of_exponent_le hNr.le hloglower
    have hupper : (p 0 : ℝ) ≤ (N : ℝ) ^ (actualSelectedSubproductUpper 1 theta - e / 3) := by
      rw [← rpow_actualSelectedPrimeCoordinates (N : ℝ) hNr p hp 0]
      exact Real.rpow_le_rpow_of_exponent_le hNr.le (by linarith)
    have hkeylower : (p 0 : ℝ) ≤ (actualPrimeFineLabelIntegerUpper N sigma label : ℝ) := by
      exact_mod_cast actualPrimeFineLabelFinset_le_integerUpper hlabel
    refine ⟨hlo, hhi, hlevel, hlower.trans hkeylower, ?_⟩
    calc
      _ ≤ (N : ℝ) ^ sigma * p 0 := fine_key_inflation (Nat.zero_lt_of_lt hN) hlabel
      _ ≤ (N : ℝ) ^ sigma * (N : ℝ) ^ (actualSelectedSubproductUpper 1 theta - e / 3) :=
        mul_le_mul_of_nonneg_left hupper (Real.rpow_nonneg hNpos.le _)
      _ = (N : ℝ) ^ (sigma + (actualSelectedSubproductUpper 1 theta - e / 3)) :=
        (Real.rpow_add hNpos _ _).symm
      _ ≤ (N : ℝ) ^ (actualSelectedSubproductUpper 1 theta - e / 4) :=
        Real.rpow_le_rpow_of_exponent_le hNr.le (by linarith)
  · exact (not_lt_of_ge hclose hgap).elim

/-- Cancellation uses every ORIGINAL prefix square after the first slot.
No arbitrary selected mask or supplied selected-square gate is used. -/
theorem first_slot_complement_squares {α : Type*} (key : α → ℝ)
    {D : ℝ} (label : α) (rest : List α) (hpositive : 0 < key label)
    (hfull : PrefixSquareBound key D (label :: rest)) :
    PrefixSquareBound key (D / key label) rest := by
  intro i hi
  have hh := suffix_square key (prefix := [label]) (rest := rest) hfull i hi
  apply (le_div_iff₀ hpositive).mpr
  simpa [wp, mul_assoc, mul_comm, mul_left_comm] using hh

/-- The remaining slot lists are computed once on the same canonical keys.
The right-bin bound is proved by the existing allocator, not supplied. -/
theorem fixed_head_complement_allocation {α : Type*} (key : α → ℝ)
    {D A : ℝ} (label : α) (rest : List α)
    (hA : 1 ≤ A) (hpositive : 0 < key label)
    (hC : 1 ≤ D / (A * key label))
    (hfull : PrefixSquareBound key D (label :: rest)) :
    let ac := actualTwoCapacityGreedy key A rest
    BoxPartition ac.1 ac.2 rest ∧
      wp key ac.1 ≤ A ∧ wp key ac.2 ≤ D / (A * key label) ∧
      (ac.1 ++ [label] ++ ac.2).Perm (label :: rest) := by
  have hApos : 0 < A := zero_lt_one.trans_le hA
  have hAC : A * (D / (A * key label)) = D / key label := by
    field_simp [hApos.ne', hpositive.ne']
    <;> ring
  have hs := first_slot_complement_squares key label rest hpositive hfull
  rw [← hAC] at hs
  obtain ⟨hpart, hleft, hright⟩ := actualTwoCapacityGreedy_correct key hA hC rest hs
  refine ⟨hpart, hleft, hright, ?_⟩
  have hmove :
      ((actualTwoCapacityGreedy key A rest).1 ++ [label] ++ (actualTwoCapacityGreedy key A rest).2).Perm
        ([label] ++ ((actualTwoCapacityGreedy key A rest).1 ++ (actualTwoCapacityGreedy key A rest).2)) := by
    simpa only [List.append_assoc] using
      (List.perm_append_comm (l₁ := (actualTwoCapacityGreedy key A rest).1) (l₂ := [label])).append_right
        (actualTwoCapacityGreedy key A rest).2
  exact hmove.trans (hpart.perm.append_left [label])

private theorem coordinates_of_shape {N : ℕ} {history tail : List ℕ}
    (p : Fin 3 → ℕ) (hshape : history.reverse = p 0 :: p 1 :: p 2 :: tail) :
    primeHistoryLogCoordinates (N : ℝ) 3 (rosserAncestor 3 history) =
      actualSelectedPrimeCoordinates (N : ℝ) p := by
  have hh : history = tail.reverse ++ [p 2, p 1, p 0] := by
    simpa [List.reverse_cons, List.append_assoc] using congrArg List.reverse hshape
  rw [hh, rosserAncestor_append 3 tail.reverse [p 2, p 1, p 0] (by simp)]
  have hself : rosserAncestor 3 [p 2, p 1, p 0] = [p 2, p 1, p 0] := by simp [rosserAncestor]
  rw [hself]
  funext i
  fin_cases i <;> simp [primeHistoryLogCoordinates, primeHistoryTuple,
    actualPrimeTupleLog, actualSelectedPrimeCoordinates]

/-- The actual retained close winner supplies both the head's critical
interval and ALL complementary fine-key squares, with no support premise.
The subsequent conditional is the literal numerical capacity case. -/
theorem actual_close_retained_fine_head
    (e h sigma : ℝ) (m N cap k : ℕ) (hk : 3 ≤ k) (w z : ℝ) (weight : ℕ → ℝ)
    (state : FirstExitDepthState ℕ)
    (hstate : state ∈ firstExitDepthFrontier k
      (actualExtendedThirdCompactUpperPolicy e h m N) weight [] true 1
      (roughPrimeUniverse N cap w z))
    (hN : 2 ≤ N) (he0 : 0 < e) (he : e ≤ 1 / 384)
    (hsigma0 : 0 ≤ sigma) (hsigma : sigma ≤ e / 64)
    (hwidth : sigma * (k + 1) ≤ e / 2)
    (hmesh : actualExtendedThirdDyadicStep m ≤ e / 32)
    {j : ActualExtendedThirdDyadicLabel m} (hj : j ∈ actualExtendedThirdCompactCells e h m)
    (howned : primeHistoryLogCoordinates (N : ℝ) 3 (rosserAncestor 3 state.selectedPrefix) ∈
      actualExtendedThirdOwnedCell m j)
    (hfull : actualExtendedThirdDyadicHi m j 0 ≤ mu - 4 * e)
    {t : Fin 3 → ℝ} (ht : t ∈ actualExtendedThirdPhysicalCell m j)
    (hwinner : actualExtendedThirdLeastWinningIndex e m j = 4)
    (hclose : wInner (t 0) (t 1) (t 2) - v (t 0) ≤ e / 4)
    (p : Fin 3 → ℕ) (primeTail : List ℕ)
    (hshape : state.selectedPrefix.reverse = p 0 :: p 1 :: p 2 :: primeTail)
    (label : ℕ) (rest : List ℕ)
    (hatom : state.selectedPrefix.reverse ∈ actualPrimeSlotBox (actualPrimeFineLabelFinset N sigma)
      (label :: rest)) :
    let theta := actualExtendedThirdBaseParameter e m j
    let D := (N : ℝ) ^ (theta - e / 32)
    let key := fun l => (actualPrimeFineLabelIntegerUpper N sigma l : ℝ)
    (N : ℝ) ^ (2 * theta - 1 + e) ≤ key label ∧
      key label ≤ (N : ℝ) ^ (actualSelectedSubproductUpper 1 theta - e / 4) ∧
      PrefixSquareBound key D (label :: rest) ∧
      PrefixSquareBound key (D / key label) rest ∧
      ∀ A : ℝ, 1 ≤ A → 1 ≤ D / (A * key label) →
        let ac := actualTwoCapacityGreedy key A rest
        BoxPartition ac.1 ac.2 rest ∧ wp key ac.1 ≤ A ∧
          wp key ac.2 ≤ D / (A * key label) ∧
          (ac.1 ++ [label] ++ ac.2).Perm (label :: rest) ∧
          ∀ ps ∈ actualPrimeSlotBox (actualPrimeFineLabelFinset N sigma) (label :: rest),
            ∃ ls ms rs,
              ls ∈ actualPrimeSlotBox (actualPrimeFineLabelFinset N sigma) ac.1 ∧
              ms ∈ actualPrimeSlotBox (actualPrimeFineLabelFinset N sigma) [label] ∧
              rs ∈ actualPrimeSlotBox (actualPrimeFineLabelFinset N sigma) ac.2 ∧
              ls.prod * ms.prod * rs.prod = ps.prod ∧
              (ls.prod : ℝ) ≤ wp key ac.1 ∧ (ms.prod : ℝ) ≤ wp key [label] ∧
              (rs.prod : ℝ) ≤ wp key ac.2 := by
  have hNnat : 1 < N := by omega
  have hNr : (1 : ℝ) < N := by exact_mod_cast hNnat
  have hsub := mem_firstExitDepthFrontier_selected_reverse_sublist k
    (actualExtendedThirdCompactUpperPolicy e h m N) weight
    (roughPrimeUniverse N cap w z) state hstate
  have hp (i : Fin 3) : 0 < p i := by
    have hm : p i ∈ state.selectedPrefix.reverse := by rw [hshape]; fin_cases i <;> simp
    exact (mem_roughPrimeUniverse_prime (hsub.subset hm)).pos
  have hs : actualSelectedPrimeCoordinates (N : ℝ) p ∈ actualExtendedThirdPhysicalCell m j := by
    have hh := actualExtendedThirdOwnedCell_subset_physicalCell m j howned
    rwa [coordinates_of_shape p hshape] at hh
  have hlabel : p 0 ∈ actualPrimeFineLabelFinset N sigma label := by
    rw [hshape] at hatom
    obtain ⟨⟨q, qs⟩, hmem, heq⟩ := Finset.mem_image.mp hatom
    rcases List.cons.inj heq with ⟨rfl, rfl⟩
    exact (Finset.mem_product.mp hmem).1
  obtain ⟨hlo, hhi, hlevel, hkeylo, hkeyhi⟩ := actual_close_fine_head_bounds
    he0 he hsigma hmesh hfull ht hwinner hclose hNnat p hp hs label hlabel
  have hkeypos : (0 : ℝ) < actualPrimeFineLabelIntegerUpper N sigma label :=
    (Real.rpow_pos_of_pos (zero_lt_one.trans hNr) _).trans_le hkeylo
  have hbudget : (Real.log (N : ℝ) / Real.log (N : ℝ)) *
      actualExtendedThirdPhysicalLevel e m j + sigma * (k + 1) ≤
        actualExtendedThirdBaseParameter e m j - e / 32 := by
    rw [div_self (Real.log_pos hNr).ne']
    linarith
  have hsquares := actual_frontier_fine_word_support e h m N cap k hk w z weight state hstate
    hj howned sigma (N : ℝ) sigma (actualExtendedThirdBaseParameter e m j - e / 32)
    (Nat.zero_lt_of_lt hNnat) hNr hsigma0 le_rfl (label :: rest) hatom hbudget
  refine ⟨hkeylo, hkeyhi, hsquares,
    first_slot_complement_squares _ label rest hkeypos hsquares, ?_⟩
  intro A hA hC
  obtain ⟨hpart, hleft, hright, hperm⟩ :=
    fixed_head_complement_allocation _ label rest hA hkeypos hC hsquares
  refine ⟨hpart, hleft, hright, hperm, ?_⟩
  exact whole_atom_same_bins N sigma
    (g := ⟨(actualTwoCapacityGreedy
      (fun l => (actualPrimeFineLabelIntegerUpper N sigma l : ℝ)) A rest).1,
      [label], (actualTwoCapacityGreedy
        (fun l => (actualPrimeFineLabelIntegerUpper N sigma l : ℝ)) A rest).2⟩) hperm

end

end ImbalancedChen.Part3.ActualWCloseFineHead
