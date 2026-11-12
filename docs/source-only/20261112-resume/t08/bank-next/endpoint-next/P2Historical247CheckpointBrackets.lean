import ImbalancedChen.P2Historical248Authentication

/-! The two actual saved arrays bound generation 247. No generation-247
snapshot or last winning action is presumed. -/
namespace ImbalancedChen.P2Historical247CheckpointBrackets

noncomputable section
open P2Historical248Authentication P2HistoricalLowerBankAncestry P2TableActionSourceOnly

private theorem history_mono (side : Bool) (i : Fin 200) :
    Monotone (fun n => iterate designatedW1 designatedW2 n side i) :=
  monotone_nat_of_le_succ (fun n => iterate_retains designatedW1 designatedW2 n side i)

/-- The checkpoints retain both sides and the same physical grid index. -/
theorem historical_247_bracket (side : Bool) (i : Fin 200) :
    snapshot json184 side i ≤ iterate designatedW1 designatedW2 247 side i ∧
    iterate designatedW1 designatedW2 247 side i ≤ snapshot json248 side i := by
  have hlo := stage184_guard side i
  have hhi := stage248_guard side i
  rw [sourceIterate_eq 184] at hlo
  rw [sourceIterate_eq 248] at hhi
  rw [← hlo, ← hhi]
  exact ⟨history_mono side i (by decide : 184 ≤ 247),
    iterate_retains designatedW1 designatedW2 247 side i⟩

theorem historical_upper_247_real_bracket (i : Fin 200) :
    (snapshot json184 true i : ℝ)/tableQ ≤ (iterate designatedW1 designatedW2 247 true i : ℝ)/tableQ ∧
    (iterate designatedW1 designatedW2 247 true i : ℝ)/tableQ ≤ (snapshot json248 true i : ℝ)/tableQ := by
  obtain ⟨hl,hr⟩ := historical_247_bracket true i
  exact ⟨div_le_div_of_nonneg_right (by exact_mod_cast hl) (Nat.cast_nonneg tableQ),
    div_le_div_of_nonneg_right (by exact_mod_cast hr) (Nat.cast_nonneg tableQ)⟩

end
end ImbalancedChen.P2Historical247CheckpointBrackets
