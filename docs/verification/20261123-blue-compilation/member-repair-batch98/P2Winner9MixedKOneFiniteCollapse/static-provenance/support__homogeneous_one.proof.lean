by
  classical
  let oneHot (i : Fin 9) : Fin 9 → Fin 2 :=
    fun r => if r = i then 1 else 0
  have hsum (i : Fin 9) : (∑ r : Fin 9, (oneHot i r).val) = 1 := by
    simp [oneHot, apply_ite]
  have hprod (i : Fin 9) :
      (∏ r : Fin 9, y r ^ (oneHot i r).val) = y i := by
    calc
      _ = ∏ r : Fin 9, if r = i then y r else 1 := by
        apply Finset.prod_congr rfl
        intro r hr
        by_cases h : r = i <;> simp [oneHot, h]
      _ = _ := by simp
  have hnat : homogeneous y 1 = ∑ i : Fin 9, y i := by
    unfold homogeneous
    change (∑ α : Fin 9 → Fin 2,
      if (∑ r : Fin 9, (α r).val) = 1 then
        ∏ r : Fin 9, y r ^ (α r).val else 0) = ∑ i : Fin 9, y i
    rw [← Finset.sum_filter]
    symm
    refine Finset.sum_bij (fun i _ => oneHot i) ?_ ?_ ?_ ?_
    · intro i hi
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsum i⟩
    · intro i hi k hk heq
      by_contra hne
      have hv := congrArg (fun f : Fin 9 → Fin 2 => (f i).val) heq
      have : (1 : ℕ) = 0 := by simpa [oneHot, hne] using hv
      omega
    · intro α hα
      have htotal : (∑ r : Fin 9, (α r).val) = 1 :=
        (Finset.mem_filter.mp hα).2
      have hsome : ∃ i : Fin 9, α i ≠ 0 := by
        by_contra hn
        push_neg at hn
        have hz : (∑ r : Fin 9, (α r).val) = 0 := by simp [hn]
        omega
      obtain ⟨i, hi⟩ := hsome
      have hione : (α i).val = 1 := by
        have hlt := (α i).isLt
        have hne : (α i).val ≠ 0 := by
          intro hz
          apply hi
          apply Fin.ext
          simpa using hz
        omega
      have hrest : (∑ r ∈ (Finset.univ : Finset (Fin 9)).erase i,
          (α r).val) = 0 := by
        have he := Finset.sum_erase_add (Finset.univ : Finset (Fin 9))
          (fun r => (α r).val) (Finset.mem_univ i)
        rw [htotal, hione] at he
        omega
      refine ⟨i, Finset.mem_univ i, ?_⟩
      funext r
      by_cases hr : r = i
      · subst r
        simp only [oneHot, if_pos rfl]
        apply Fin.ext
        simpa using hione.symm
      · simp only [oneHot, if_neg hr]
        have hmem : r ∈ (Finset.univ : Finset (Fin 9)).erase i := by
          simp [hr]
        have hle := Finset.single_le_sum
          (fun r (_ : r ∈ (Finset.univ : Finset (Fin 9)).erase i) =>
            Nat.zero_le (α r).val) hmem
        rw [hrest] at hle
        apply Fin.ext
        simpa using (Nat.eq_zero_of_le_zero hle).symm
    · intro i hi
      exact (hprod i).symm
  exact_mod_cast hnat
