import ImbalancedChen.Part3ActualWCloseFineHead

/-!
# The actual W-close below-one full-vector repair

SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

The manuscript prescribes reassigning ALL original slots to A,D/A when
the selected complement capacity is below one. The third list is empty
and its product is one; it is not bounded by the rejected capacity.

This module implements that exact frozen-label choice and proves both
capacity branches from actual retained W-close source support. The original
head key is used only to prove D/A < headKey in the repair branch; it is
not asserted to remain a final factor. Every original atom tuple retains
its full product on the same computed label partition.
-/

namespace ImbalancedChen.Part3.ActualWCloseFullRepair

noncomputable section

open scoped Classical
open ActualWThreeCapacityRun ActualWFineWordAdapter ActualWCloseFineHead VariableEnvelope
open MathlibNt.SieveTheory.LiLiuPrereqWFBoxAllocation

/-- Generic original-label full-vector repair. Its third bin is exactly
empty, not a hypothetical integer factor below one. -/
theorem original_word_full_repair {α : Type*} (key : α → ℝ) {D A : ℝ}
    (label : α) (rest : List α) (hA : 1 ≤ A) (hDA : 1 ≤ D / A)
    (hkey : 0 < key label) (hsmall : D / (A * key label) < 1)
    (hsquares : PrefixSquareBound key D (label :: rest)) :
    let ab := actualTwoCapacityGreedy key A (label :: rest)
    D / A < key label ∧ BoxPartition ab.1 ab.2 (label :: rest) ∧
      wp key ab.1 ≤ A ∧ wp key ab.2 ≤ D / A ∧
      (ab.1 ++ ab.2 ++ ([] : List α)).Perm (label :: rest) := by
  have hApos : 0 < A := zero_lt_one.trans_le hA
  have hsplit : A * (D / A) = D := by field_simp [hApos.ne'] <;> ring
  have hfull : PrefixSquareBound key (A * (D / A)) (label :: rest) := by
    rwa [hsplit]
  obtain ⟨hpart, hleft, hright⟩ := actualTwoCapacityGreedy_correct key hA hDA (label :: rest) hfull
  have hDlt : D < A * key label := (div_lt_one (mul_pos hApos hkey)).mp hsmall
  have hDAkey : D / A < key label :=
    (div_lt_iff₀ hApos).mpr (by simpa only [mul_comm] using hDlt)
  exact ⟨hDAkey, hpart, hleft, hright, by simpa only [List.append_nil] using hpart.perm⟩

/-- One program on the original key word, with the genuine below-one
repair as its second branch. All tuple-level factors use these same lists. -/
def closeSlots (N : ℕ) (sigma D A : ℝ) (label : ℕ) (rest : List ℕ) : Bins ℕ :=
  let key := fun l => (actualPrimeFineLabelIntegerUpper N sigma l : ℝ)
  if 1 ≤ D / (A * key label) then
    let ac := actualTwoCapacityGreedy key A rest
    ⟨ac.1, [label], ac.2⟩
  else
    let ab := actualTwoCapacityGreedy key A (label :: rest)
    ⟨ab.1, ab.2, []⟩

/-- Numerical correctness of BOTH literal branches, with original slot
permutation and the valid capacities stated separately. -/
theorem closeSlots_correct (N : ℕ) (sigma : ℝ) {D A : ℝ}
    (label : ℕ) (rest : List ℕ) (hA : 1 ≤ A) (hDA : 1 ≤ D / A)
    (hkey : (0 : ℝ) < actualPrimeFineLabelIntegerUpper N sigma label)
    (hfull : PrefixSquareBound (fun l => (actualPrimeFineLabelIntegerUpper N sigma l : ℝ)) D
      (label :: rest)) :
    let key := fun l => (actualPrimeFineLabelIntegerUpper N sigma l : ℝ)
    let out := closeSlots N sigma D A label rest
    (flatten out).Perm (label :: rest) ∧ wp key out.left ≤ A ∧
      ((1 ≤ D / (A * key label) ∧ out.middle = [label] ∧ wp key out.right ≤ D / (A * key label)) ∨
        (D / (A * key label) < 1 ∧ out.right = [] ∧
          wp key out.middle ≤ D / A ∧ D / A < key label)) := by
  let key := fun l => (actualPrimeFineLabelIntegerUpper N sigma l : ℝ)
  by_cases hC : 1 ≤ D / (A * key label)
  · have hs := fixed_head_complement_allocation key label rest hA hkey hC hfull
    obtain ⟨hpart, hleft, hright, hperm⟩ := hs
    simp only [closeSlots, if_pos hC, flatten]
    exact ⟨hperm, hleft, Or.inl ⟨hC, rfl, hright⟩⟩
  · have hsmall := lt_of_not_ge hC
    obtain ⟨hlt, hpart, hleft, hright, hperm⟩ :=
      original_word_full_repair key label rest hA hDA hkey hsmall hfull
    simp only [closeSlots, if_neg hC, flatten]
    exact ⟨hperm, hleft, Or.inr ⟨hsmall, rfl, hright, hlt⟩⟩

/-- The actual covering range guarantees a valid new second capacity,
strictly greater than one. The rejected C never appears in this bound. -/
theorem actual_close_repair_capacity {N : ℕ} {e theta A : ℝ}
    (hN : 1 < N) (he : e ≤ 1 / 384) (htheta : 1 / 2 ≤ theta)
    (hA : 1 ≤ A) (hAupper : A ≤ (N : ℝ) ^ (1 / 3 : ℝ)) :
    1 < (N : ℝ) ^ (theta - e / 32) / A := by
  have hNr : (1 : ℝ) < N := by exact_mod_cast hN
  have hApos : 0 < A := zero_lt_one.trans_le hA
  apply (lt_div_iff₀ hApos).mpr
  have hh : (N : ℝ) ^ (1 / 3 : ℝ) < (N : ℝ) ^ (theta - e / 32) :=
    Real.rpow_lt_rpow_of_exponent_lt hNr (by linarith)
  simpa only [one_mul] using hAupper.trans_lt hh

/-- Complete actual W-close frozen-atom allocation, including C<1.
Both original support and head geometry come from the real retained
winner. The branch is computed, not supplied as a factorization premise. -/
theorem actual_W_close_complete_atom
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
      (label :: rest))
    (A : ℝ) (hA : 1 ≤ A) (hAupper : A ≤ (N : ℝ) ^ (1 / 3 : ℝ)) :
    let theta := actualExtendedThirdBaseParameter e m j
    let D := (N : ℝ) ^ (theta - e / 32)
    let key := fun l => (actualPrimeFineLabelIntegerUpper N sigma l : ℝ)
    let out := closeSlots N sigma D A label rest
    1 < D / A ∧ (flatten out).Perm (label :: rest) ∧ wp key out.left ≤ A ∧
      ((1 ≤ D / (A * key label) ∧ out.middle = [label] ∧ wp key out.right ≤ D / (A * key label)) ∨
        (D / (A * key label) < 1 ∧ out.right = [] ∧
          wp key out.middle ≤ D / A ∧ D / A < key label)) ∧
      ∀ ps ∈ actualPrimeSlotBox (actualPrimeFineLabelFinset N sigma) (label :: rest),
        ∃ ls ms rs,
          ls ∈ actualPrimeSlotBox (actualPrimeFineLabelFinset N sigma) out.left ∧
          ms ∈ actualPrimeSlotBox (actualPrimeFineLabelFinset N sigma) out.middle ∧
          rs ∈ actualPrimeSlotBox (actualPrimeFineLabelFinset N sigma) out.right ∧
          ls.prod * ms.prod * rs.prod = ps.prod ∧
          (ls.prod : ℝ) ≤ wp key out.left ∧ (ms.prod : ℝ) ≤ wp key out.middle ∧
          (rs.prod : ℝ) ≤ wp key out.right := by
  obtain ⟨hkeylower, hkeyupper, hsquares, hrest, hselected⟩ := actual_close_retained_fine_head
    e h sigma m N cap k hk w z weight state hstate hN he0 he hsigma0 hsigma hwidth hmesh
    hj howned hfull ht hwinner hclose p primeTail hshape label rest hatom
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hkey : (0 : ℝ) < actualPrimeFineLabelIntegerUpper N sigma label :=
    (Real.rpow_pos_of_pos (zero_lt_one.trans hNr) _).trans_le hkeylower
  have htheta := (actualExtendedThirdBaseParameter_range he0 he ⟨t, ht⟩ hfull).1
  have hDA := actual_close_repair_capacity (by omega : 1 < N) he htheta hA hAupper
  obtain ⟨hperm, hleft, hcases⟩ := closeSlots_correct N sigma label rest hA hDA.le hkey hsquares
  exact ⟨hDA, hperm, hleft, hcases, whole_atom_same_bins N sigma hperm⟩

/-- In the repair branch the third arithmetic factor is literally one.
This holds on the original empty group box without a capacity assumption. -/
theorem empty_group_product (N : ℕ) (sigma : ℝ) (rs : List ℕ)
    (hrs : rs ∈ actualPrimeSlotBox (actualPrimeFineLabelFinset N sigma) []) :
    rs = [] ∧ rs.prod = 1 := by
  have hr : rs = [] := by simpa [actualPrimeSlotBox] using hrs
  exact ⟨hr, by simp [hr]⟩

end

end ImbalancedChen.Part3.ActualWCloseFullRepair
