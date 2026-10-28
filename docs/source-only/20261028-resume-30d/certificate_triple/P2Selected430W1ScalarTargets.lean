import ImbalancedChen.P2Selected430CausalOccurrenceExporter

/-! Source-only / uncompiled. The actual literal target arrays, not an
assumed selected-action target licence, imply the physical W1 target gate.
The closed70-row transcription proof below is not executed here. -/
namespace ImbalancedChen.P2Selected430W1ScalarTargets
noncomputable section
open P2Selected430LiteralActionData
open P2Selected430CausalOccurrenceExporter
open P5OriginalActionMassBound (W1Target)

/-- Literal target lists are exactly the original right-endpoint grid
prefixes of the W1 s=12/5+i/10 action. -/
theorem first70_targets (k : Fin 70) :
    (rows ⟨k.val,by have := k.isLt; omega⟩).targets =
      List.range (70+5*(k.val/10)) := by
  fin_cases k <;> rfl

theorem W1_label_first70 {k : Fin 106} {ij : Fin 7 × Fin 10}
    (h : (rows k).w1Label = some ij) : k.val < 70 := by
  by_contra hn
  have hk : 70 ≤ k.val := by omega
  let l : Fin 36 := ⟨k.val-70,by have := k.isLt; omega⟩
  have heq : (⟨70+l.val,by have := l.isLt; omega⟩ : Fin 106) = k := by
    apply Fin.ext
    dsimp [l]
    omega
  have hnone := last36_w1Label_none l
  rw [heq,h] at hnone
  cases hnone

/-- A selected W1 row really covers this right-endpoint grid query.
No arbitrary hTarget premise is used. -/
theorem selectedW1_cell_target {g : Fin 430} {cell : Fin 200}
    {ij : Fin 7 × Fin 10} (h : selectedW1 g cell = some ij) :
    1+((cell.val : ℝ)+1)/50 ≤ W1Target ij.1 := by
  obtain ⟨k,hchoice,hlabel,hmem,hvalue⟩ := selectedW1_source h
  have hk := W1_label_first70 hlabel
  let l : Fin 70 := ⟨k.val,hk⟩
  have hlabel' := first70_w1Label l
  have hkl : (⟨l.val,by have := l.isLt; omega⟩ : Fin 106) = k := by
    apply Fin.ext
    rfl
  rw [hkl,hlabel] at hlabel'
  have hij : ij =
      (⟨l.val/10,by have := l.isLt; omega⟩,
        ⟨l.val%10,Nat.mod_lt _ (by norm_num)⟩) := Option.some.inj hlabel'
  have htargets := first70_targets l
  rw [hkl] at htargets
  rw [htargets,List.mem_range] at hmem
  have hnat : cell.val+1 ≤ 70+5*ij.1.val := by
    rw [hij]
    exact Nat.succ_le_of_lt hmem
  have hreal : (cell.val : ℝ)+1 ≤ 70+5*(ij.1.val : ℝ) := by
    exact_mod_cast hnat
  dsimp [W1Target]
  linarith

theorem selectedW1_actual_argument_target {g : Fin 430} {cell : Fin 200}
    {ij : Fin 7 × Fin 10} {s : ℝ}
    (h : selectedW1 g cell = some ij) (hs : s ∈ queryCell cell) :
    s ≤ W1Target ij.1 :=
  hs.2.trans (selectedW1_cell_target h)

/-- This is the original physical comparison-cutoff admission, converted
to the chosen W1 target using the actual selected row's grid support. -/
theorem selectedW1_actual_ceiling {g : Fin 430} {cell : Fin 200}
    {ij : Fin 7 × Fin 10} {s L chi : ℝ}
    (h : selectedW1 g cell = some ij) (hs : s ∈ queryCell cell)
    (hL : 0 ≤ L) (hphysical : L/s ≤ chi) :
    L/W1Target ij.1 ≤ chi := by
  have htarget := selectedW1_actual_argument_target h hs
  have hs0 : 0 < s := by
    have hcell := hs.1
    change 1+(cell.val : ℝ)/50 ≤ s at hcell
    have hval := Nat.cast_nonneg (R := ℝ) cell.val
    linarith
  exact (div_le_div_of_nonneg_left hL hs0 htarget).trans hphysical

end
end ImbalancedChen.P2Selected430W1ScalarTargets
