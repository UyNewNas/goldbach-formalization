import ImbalancedChen.P2Historical248Authentication

/-! Actual original W2 price fields as a single directed subtraction.
The ordinary total and the two switched mass enclosures are analytic
inputs, separate from authentication of the historical integer fields. -/
namespace ImbalancedChen.P2HistoricalW2BaseRepricing

noncomputable section
open P2TableActionSourceOnly P2HistoricalSourceJSON P2Historical248Authentication

def originalBase (v : Value) : ℤ := integer (field v "base_lower_numerator")
def updatedBase (u : Value) : ℤ := integer (field u "new_base")
def coarseBase (v : Value) : ℤ := integer (field v "coarse_base_lower_numerator")
def saving (v : Value) : ℚ := rational (field v "seed_gain_lower")

def addedSaving (v : Value) : ℚ :=
  let r := field v "variable_kernel_saving"
  if text r = "null" then 0 else saving r

private theorem q_pos : (0 : ℚ)<tableQ := by exact_mod_cast tableQ_pos

private theorem floor_price (x : ℚ) : (⌊(tableQ : ℚ)*x⌋ : ℚ)/tableQ ≤ x := by
  exact (div_le_iff₀ q_pos).mpr (by simpa only [mul_comm] using Int.floor_le ((tableQ : ℚ)*x))

private theorem recalibration_le (v : Value) {K mass : ℚ} (hK : K≤681/100)
    (hm : positiveCost v ≤ (681/100)*mass/4) :
    (w2Recalibration K v : ℚ)/tableQ ≤ ((681/100-K)*mass)/20 := by
  unfold w2Recalibration
  have hh := floor_price ((681/100-K)*positiveCost v/(5*(681/100)))
  have hr : (tableQ:ℚ)*(681/100-K)*positiveCost v/(5*(681/100)) =
      (tableQ:ℚ)*((681/100-K)*positiveCost v/(5*(681/100))) := by ring
  rw [hr]
  apply hh.trans
  have hmul := mul_le_mul_of_nonneg_left hm (sub_nonneg.mpr hK)
  norm_num at hmul ⊢
  nlinarith only [hmul]

/-- The stage-56 change uses the lower positive old cost for one price
reduction. The bad Gamma5 replacement is part of that old positive cost. -/
theorem lower_K_base {v u : Value} (h : w2LowerUpdateOK (v,u) = true)
    {ordinary oldMass : ℚ}
    (h₀ : (originalBase v : ℚ)/tableQ ≤ (ordinary-(681/100)*oldMass/4)/5)
    (hm : positiveCost v ≤ (681/100)*oldMass/4) :
    (updatedBase u : ℚ)/tableQ ≤ (ordinary-(67633/10000)*oldMass/4)/5 := by
  simp only [w2LowerUpdateOK,decide_eq_true_eq] at h
  have hbase : updatedBase u = originalBase v + w2Recalibration (67633/10000) v :=
    h.2.2.2.2
  have hc := recalibration_le v (by norm_num : (67633/10000 : ℚ)≤681/100) hm
  rw [hbase,Int.cast_add,add_div]
  linarith only [h₀,hc]

/-- The stage-120 change reprices the ORIGINAL old mass and uses the
box saving once at the new K. Both terms together account for the
one difference between the original and the new switched charges. -/
theorem variable_kernel_base {v u s : Value} (h : w2VariableUpdateOK ((v,u),s) = true)
    {ordinary oldMass newMass : ℚ}
    (h₀ : (originalBase v : ℚ)/tableQ ≤ (ordinary-(681/100)*oldMass/4)/5)
    (hm : positiveCost v ≤ (681/100)*oldMass/4)
    (hs : saving s ≤ (67619/10000)*(oldMass-newMass)/20) :
    (updatedBase u : ℚ)/tableQ ≤ (ordinary-(67619/10000)*newMass/4)/5 := by
  simp only [w2VariableUpdateOK,decide_eq_true_eq] at h
  have hbase : updatedBase u = originalBase v + w2Recalibration (67619/10000) v +
      ⌊(tableQ : ℚ)*saving s⌋ := h.2.2.2.2.2.2
  have hc := recalibration_le v (by norm_num : (67619/10000 : ℚ)≤681/100) hm
  have hf := (floor_price (saving s)).trans hs
  rw [hbase,Int.cast_add,Int.cast_add,add_div,add_div]
  linarith only [h₀,hc,hf]

/-- Each added action's coarse base already uses the new K. Its only
allowed adjustment is the box saving in the same row. The null field
means zero, and no savings are imputed to an absent certificate. -/
theorem added_base {v : Value} (h : w2AddedBaselineOK v = true)
    {ordinary oldMass newMass : ℚ}
    (h₀ : (coarseBase v : ℚ)/tableQ ≤ (ordinary-(67619/10000)*oldMass/4)/5)
    (hs : addedSaving v ≤ (67619/10000)*(oldMass-newMass)/20) :
    (originalBase v : ℚ)/tableQ ≤ (ordinary-(67619/10000)*newMass/4)/5 := by
  simp only [w2AddedBaselineOK, Bool.and_eq_true, decide_eq_true_eq] at h
  have hb : integer (field v "variable_kernel_seed_floor") =
      (if text (field v "variable_kernel_saving") = "null" then 0
       else ⌊(tableQ : ℚ)*saving (field v "variable_kernel_saving")⌋) ∧
      originalBase v = coarseBase v + integer (field v "variable_kernel_seed_floor") := by
    unfold saving originalBase coarseBase
    tauto
  have hfloor : integer (field v "variable_kernel_seed_floor") = ⌊(tableQ : ℚ)*addedSaving v⌋ := by
    rw [hb.1,addedSaving]
    split_ifs <;> simp
  have hf := (floor_price (addedSaving v)).trans hs
  rw [hb.2,hfloor,Int.cast_add,add_div]
  linarith only [h₀,hf]

end
end ImbalancedChen.P2HistoricalW2BaseRepricing
