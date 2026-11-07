import ImbalancedChen.P5SelectedRealEndpointSupport

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Deterministic REAL-upper whole-atom selected-mask groups. The ORIGINAL
capacity test is decided once from the full endpoint vector; the low
capacity repair reruns the full label vector. Every actual prime tuple
uses these same lists. Products, capacities, label-word permutation and
the extra common-beta group3 endpoint exponent are all explicit.
No W initialization or Medium/PP licence is asserted here.
-/
namespace ImbalancedChen.P5Z.SelectedRealWholeAtomGroups
noncomputable section
open Classical
open scoped BigOperators
open U11Integral U1011OriginalSixteenPolicyBank
open PresievedRoughSlotAffineGates SelectedRealEndpointSupport
open MathlibNt.SieveTheory.LiLiuPrereqWFBoxAllocation

def selectedLabels (p : Policy) (r : ℕ) : List (Fin 4 ⊕ Fin r) := (selectedFront p).map Sum.inl

def weight {r : ℕ} (N : ℕ) (u : Fin 4 → ℝ) (v : Fin r → ℝ) (i : Fin 4 ⊕ Fin r) : ℝ :=
  (N : ℝ) ^ exponent u v i

def middleEndpoint (N : ℕ) (p : Policy) (u : Fin 4 → ℝ) : ℝ := (N : ℝ) ^ selectedMass p u

def groups {r : ℕ} (N : ℕ) (p : Policy) (u : Fin 4 → ℝ) (v : Fin r → ℝ) (level A : ℝ) :
    List (Fin 4 ⊕ Fin r) × List (Fin 4 ⊕ Fin r) × List (Fin 4 ⊕ Fin r) :=
  if 1 ≤ (N : ℝ) ^ level / (A * middleEndpoint N p u) then
    let ac := actualTwoCapacityGreedy (weight N u v) A (remainingLabels p r)
    (ac.1, selectedLabels p r, ac.2)
  else
    let ab := actualTwoCapacityGreedy (weight N u v) A (wholeLabels r)
    (ab.1, ab.2, [])

theorem selected_remaining_partition (p : Policy) (r : ℕ) :
    (selectedLabels p r ++ remainingLabels p r).Perm (wholeLabels r) := by
  have h := ((front_partition p).map (Sum.inl : Fin 4 → Fin 4 ⊕ Fin r)).append_right
    ((List.finRange r).map Sum.inr)
  simpa only [selectedLabels, remainingLabels, wholeLabels, List.map_append, List.append_assoc] using h

/-- The very lists chosen from REAL endpoints partition occurrences of
all four original prefix primes and all original rough slots. -/
theorem groups_partition {r : ℕ} (N : ℕ) (p : Policy) (u : Fin 4 → ℝ)
    (v : Fin r → ℝ) (level A : ℝ) :
    let out := groups N p u v level A
    (out.1 ++ out.2.1 ++ out.2.2).Perm (wholeLabels r) := by
  unfold groups
  split_ifs with hc
  · let ac := actualTwoCapacityGreedy (weight N u v) A (remainingLabels p r)
    have hp := actualTwoCapacityGreedy_partition (weight N u v) A (remainingLabels p r)
    have hm : (ac.1 ++ selectedLabels p r ++ ac.2).Perm
        (selectedLabels p r ++ (ac.1 ++ ac.2)) := by
      simpa only [List.append_assoc] using
        (List.perm_append_comm (l₁ := ac.1) (l₂ := selectedLabels p r)).append_right ac.2
    exact hm.trans ((hp.perm.append_left (selectedLabels p r)).trans (selected_remaining_partition p r))
  · simpa only [List.append_nil] using
      (actualTwoCapacityGreedy_partition (weight N u v) A (wholeLabels r)).perm

theorem selected_endpoint_product {r N : ℕ} (hN : 1 < N) (p : Policy)
    (u : Fin 4 → ℝ) (v : Fin r → ℝ) :
    ((selectedLabels p r).map (weight N u v)).prod = middleEndpoint N p u := by
  simpa only [selectedLabels, List.map_map, Function.comp_def, weight, exponent, Sum.elim_inl,
    selected_sum, middleEndpoint] using endpoint_list_product hN u (selectedFront p)

/-- Both branches have PROVED endpoint capacities from ORIGINAL log
squares and the original full residual exponent budget. No allocation
or hDwell predicate is supplied as an input. -/
theorem groups_endpoint_capacities {r N : ℕ} (hN : 1 < N) (p : Policy)
    (u : Fin 4 → ℝ) (v : Fin r → ℝ) (level ell A : ℝ)
    (hfull : ∀ j : Fin 4, fullSquare j u ≤ level)
    (hselected : ∀ j : Fin 4, ¬Selected p j → selectedSquare p j u ≤ level)
    (hv0 : ∀ i, 0 ≤ v i) (hvanti : Antitone v)
    (hcubes : ∀ i : Fin r, Even i.val → cube v i < ell)
    (hbudget : (∑ i : Fin 4, u i) + ell ≤ level)
    (hA : 1 ≤ A) (hAlevel : A ≤ (N : ℝ) ^ level) :
    let out := groups N p u v level A
    (out.1.map (weight N u v)).prod ≤ A ∧
      (((out.2.1.map (weight N u v)).prod = middleEndpoint N p u ∧
          (out.2.2.map (weight N u v)).prod ≤ (N : ℝ) ^ level / (A * middleEndpoint N p u)) ∨
        ((out.2.1.map (weight N u v)).prod ≤ (N : ℝ) ^ level / A ∧
          (out.2.2.map (weight N u v)).prod = 1)) := by
  obtain ⟨hwhole, hremain⟩ := original_endpoint_append_support hN p u v level ell
    hfull hselected hv0 hvanti hcubes hbudget
  have hApos : 0 < A := zero_lt_one.trans_le hA
  have hnpos : (0 : ℝ) < N := by exact_mod_cast (zero_lt_one.trans hN)
  have hMpos : 0 < middleEndpoint N p u := Real.rpow_pos_of_pos hnpos _
  unfold groups
  by_cases hc : 1 ≤ (N : ℝ) ^ level / (A * middleEndpoint N p u)
  · rw [if_pos hc]
    have hsplit : A * ((N : ℝ) ^ level / (A * middleEndpoint N p u)) =
        (N : ℝ) ^ (level - selectedMass p u) := by
      rw [Real.rpow_sub hnpos]
      unfold middleEndpoint
      field_simp [hApos.ne', (Real.rpow_pos_of_pos hnpos (selectedMass p u)).ne']
    rw [← hsplit] at hremain
    obtain ⟨hpart, ha, hc'⟩ := actualTwoCapacityGreedy_correct (weight N u v) hA hc (remainingLabels p r) hremain
    exact ⟨ha, Or.inl ⟨selected_endpoint_product hN p u v, hc'⟩⟩
  · rw [if_neg hc]
    have hB : 1 ≤ (N : ℝ) ^ level / A := (le_div_iff₀ hApos).mpr (by simpa using hAlevel)
    have hsplit : A * ((N : ℝ) ^ level / A) = (N : ℝ) ^ level := by field_simp [hApos.ne']
    rw [← hsplit] at hwhole
    obtain ⟨hpart, ha, hb⟩ := actualTwoCapacityGreedy_correct (weight N u v) hA hB (wholeLabels r) hwhole
    exact ⟨ha, Or.inr ⟨hb, rfl⟩⟩

/-- Any fixed fine-label dictionary maps the SAME computed occurrence
partition to the exact original atom word. This feeds original per-label
factorial normalization, without identifying a decision fibre with a box. -/
theorem groups_label_word_partition {ι : Type*} {r : ℕ} (N : ℕ) (p : Policy)
    (u : Fin 4 → ℝ) (v : Fin r → ℝ) (level A : ℝ) (labels : Fin 4 ⊕ Fin r → ι) :
    let out := groups N p u v level A
    (out.1.map labels ++ out.2.1.map labels ++ out.2.2.map labels).Perm ((wholeLabels r).map labels) := by
  simpa only [List.map_append] using (groups_partition N p u v level A).map labels

/-- A tuple is evaluated AFTER the endpoint partition. The exact natural
product and all three actual group support lengths use those fixed lists. -/
theorem groups_all_tuples {r : ℕ} (N : ℕ) (p : Policy) (u : Fin 4 → ℝ)
    (v : Fin r → ℝ) (level A : ℝ) (actual : Fin 4 ⊕ Fin r → ℕ)
    (hsize : ∀ i, (actual i : ℝ) ≤ weight N u v i) :
    let out := groups N p u v level A
    (out.1.map actual).prod * (out.2.1.map actual).prod * (out.2.2.map actual).prod =
      ((wholeLabels r).map actual).prod ∧
      ((out.1.map actual).prod : ℝ) ≤ (out.1.map (weight N u v)).prod ∧
      ((out.2.1.map actual).prod : ℝ) ≤ (out.2.1.map (weight N u v)).prod ∧
      ((out.2.2.map actual).prod : ℝ) ≤ (out.2.2.map (weight N u v)).prod := by
  have hprod := ((groups_partition N p u v level A).map actual).prod_eq
  have hbound (l : List (Fin 4 ⊕ Fin r)) : ((l.map actual).prod : ℝ) ≤ (l.map (weight N u v)).prod := by
    rw [← actualNatList_cast_prod]
    simpa only [List.map_map, Function.comp_def] using List.prod_map_le_prod_map₀
      (fun i => (actual i : ℝ)) (weight N u v) (fun i hi => Nat.cast_nonneg _) (fun i hi => hsize i)
  exact ⟨by simpa only [List.map_append, List.prod_append, mul_assoc] using hprod,
    hbound _, hbound _, hbound _⟩

/-- The COMMON beta factor belongs entirely to group3. Its endpoint cost
is ellBeta IN ADDITION TO all rough/prime label widths; e is not fixed. -/
theorem groups_beta_endpoint {r N : ℕ} (hN : 1 < N) (p : Policy)
    (u : Fin 4 → ℝ) (v : Fin r → ℝ) (level A ellBeta : ℝ)
    (actual : Fin 4 ⊕ Fin r → ℕ) (hsize : ∀ i, (actual i : ℝ) ≤ weight N u v i)
    (e : ℕ) (he : (e : ℝ) ≤ (N : ℝ) ^ ellBeta) :
    let out := groups N p u v level A
    ((out.1.map actual).prod * (out.2.1.map actual).prod * (e * (out.2.2.map actual).prod)) =
        e * ((wholeLabels r).map actual).prod ∧
      ((e * (out.2.2.map actual).prod : ℕ) : ℝ) ≤
        (N : ℝ) ^ (ellBeta + (out.2.2.map (exponent u v)).sum) := by
  have h := groups_all_tuples N p u v level A actual hsize
  refine ⟨?_, ?_⟩
  · calc
      _ = e * ((groups N p u v level A).1.map actual).prod *
          ((groups N p u v level A).2.1.map actual).prod *
          ((groups N p u v level A).2.2.map actual).prod := by ring
      _ = e * (((groups N p u v level A).1.map actual).prod *
          ((groups N p u v level A).2.1.map actual).prod *
          ((groups N p u v level A).2.2.map actual).prod) := by ring
      _ = _ := by rw [h.1]
  ·
    rw [Nat.cast_mul, Real.rpow_add (by exact_mod_cast (zero_lt_one.trans hN))]
    have hg := h.2.2.2
    have heq : ((groups N p u v level A).2.2.map (weight N u v)).prod =
        (N : ℝ) ^ ((groups N p u v level A).2.2.map (exponent u v)).sum :=
      endpoint_list_product hN (exponent u v) _
    rw [heq] at hg
    exact mul_le_mul he hg (Nat.cast_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg N) _)

end
end ImbalancedChen.P5Z.SelectedRealWholeAtomGroups
