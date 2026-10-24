import ImbalancedChen.Part5RenewalTablePrimitive
import ImbalancedChen.P5ZU11ActualH248Ordinary

/-!
Positive finite renewal transitions and their logarithmic mass. SOURCE ONLY.
The only data premises below are finite numerator inequalities, proved for
the actual H248/h248 arrays. No count bound or renewal soundness is assumed.
The existing U11 scalar atom-uniqueness theorem is reused without modification.
-/

namespace ImbalancedChen.Part5UpperTables.Renewal

noncomputable section

open Set MeasureTheory Filter
open scoped BigOperators
open Part5OriginalUpsilon5CausalDictionary

def UnitBoundedData (nums : Fin 200 → ℤ) : Prop :=
  ∀ i, (0 : ℤ) ≤ nums i ∧ nums i ≤ (2 : ℤ) ^ 80

theorem value_bounds_of_data {nums : Fin 200 → ℤ} (hn : UnitBoundedData nums) (i : Fin 200) :
    (0 : ℝ) ≤ floorValue nums i ∧ floorValue nums i ≤ 1 := by
  have hl : (0 : ℝ) ≤ (nums i : ℝ) := by exact_mod_cast (hn i).1
  have hu : (nums i : ℝ) ≤ (2 ^ 80 : ℝ) := by exact_mod_cast (hn i).2
  have hd : (0 : ℝ) < 2 ^ 80 := by positivity
  exact ⟨div_nonneg hl hd.le, (div_le_iff₀ hd).mpr (by simpa only [one_mul] using hu)⟩

theorem knot_bounds_of_data {nums : Fin 200 → ℤ} (hn : UnitBoundedData nums) (j : Fin 201) :
    (0 : ℝ) ≤ floorKnotValue nums j ∧ floorKnotValue nums j ≤ 1 := by
  unfold floorKnotValue
  split_ifs
  · exact value_bounds_of_data hn _
  · exact value_bounds_of_data hn _
  · exact ⟨le_min (value_bounds_of_data hn _).1 (value_bounds_of_data hn _).1,
      (min_le_left _ _).trans (value_bounds_of_data hn _).2⟩

theorem atom_bounds_of_data {nums : Fin 200 → ℤ} (hn : UnitBoundedData nums) (b : FloorAtom) :
    (0 : ℝ) ≤ floorAtomValue nums b ∧ floorAtomValue nums b ≤ 1 := by
  cases b with
  | inl i => exact value_bounds_of_data hn i
  | inr j => exact knot_bounds_of_data hn j

theorem upperFloor_bounds_of_data {nums : Fin 200 → ℤ} (hn : UnitBoundedData nums) (w : ℝ) :
    0 ≤ upperFloor nums w ∧ upperFloor nums w ≤ 1 := by
  by_cases he : ∃ b : FloorAtom, w ∈ upperAtomSet b
  · obtain ⟨b, hb⟩ := he
    have hv : upperFloor nums w = floorAtomValue nums b := by
      unfold upperFloor
      calc
        _ = (upperAtomSet b).indicator (fun _ => floorAtomValue nums b) w := by
          apply Finset.sum_eq_single b
          · intro c _ hcb
            exact indicator_of_notMem (fun hc => hcb
              (P5Z.U11H248.upperAtom_unique hc hb)) _
          · intro h
            exact (h (Finset.mem_univ b)).elim
        _ = _ := indicator_of_mem hb _
    rw [hv]
    exact atom_bounds_of_data hn b
  · have hz : upperFloor nums w = 0 := by
      unfold upperFloor
      apply Finset.sum_eq_zero
      intro b _
      exact indicator_of_notMem (fun hb => he ⟨b, hb⟩) _
    rw [hz]
    exact ⟨le_rfl, zero_le_one⟩

/-- The actual positive operator mass is at most log 5, independently of data. -/
theorem inverse_tail_mass_bounds (c : ℝ) :
    0 ≤ (∫ w in tailDomain c, 1 / w) ∧
      (∫ w in tailDomain c, 1 / w) ≤ Real.log 5 := by
  have hi : IntegrableOn (fun w : ℝ => 1 / w) (Ico (1 : ℝ) 5) :=
    integrableOn_one_div_Ico 5 (by norm_num)
  have hn : ∀ᵐ w : ℝ ∂volume.restrict (Ico (1 : ℝ) 5), 0 ≤ 1 / w := by
    filter_upwards [ae_restrict_mem measurableSet_Ico] with w hw
    exact div_nonneg zero_le_one (by linarith [hw.1])
  have hsub : tailDomain c ⊆ Ico (1 : ℝ) 5 := by
    intro w hw
    exact ⟨(le_max_left _ _).trans hw.1, hw.2⟩
  have hm := setIntegral_mono_set hi hn
    (Filter.Eventually.of_forall (fun w hw => hsub hw))
  have he : (∫ w : ℝ in Ico (1 : ℝ) 5, 1 / w) = Real.log 5 := by
    simpa using (integral_one_div_Ico (a := (1 : ℝ)) (b := 5) (by norm_num) (by norm_num))
  refine ⟨?_, hm.trans_eq he⟩
  apply setIntegral_nonneg measurableSet_Ico
  intro w hw
  exact div_nonneg zero_le_one (by linarith [(tailDomain_subset c hw).1])

theorem tableTail_bounds_of_data {nums : Fin 200 → ℤ} (hn : UnitBoundedData nums) (c : ℝ) :
    0 ≤ tableTail nums c ∧ tableTail nums c ≤ Real.log 5 := by
  have hw : IntegrableOn (fun w : ℝ => 1 / w) (tailDomain c) := by
    exact ((continuousOn_const.div continuousOn_id
      (fun w hw => (lt_of_lt_of_le (by norm_num) hw.1).ne')).integrableOn_compact
        isCompact_Icc).mono_set (tailDomain_subset c)
  have hc : tableTail nums c ≤ ∫ w in tailDomain c, 1 / w := by
    apply setIntegral_mono_on (integrableOn_tableTail nums c) hw measurableSet_Ico
    intro w hw'
    exact div_le_div_of_nonneg_right (upperFloor_bounds_of_data hn w).2
      (by linarith [(tailDomain_subset c hw').1])
  refine ⟨?_, hc.trans (inverse_tail_mass_bounds c).2⟩
  apply setIntegral_nonneg measurableSet_Ico
  intro w hw'
  exact div_nonneg (upperFloor_bounds_of_data hn w).1
    (by linarith [(tailDomain_subset c hw').1])

theorem adopted_h248_data_bounds : UnitBoundedData adoptedH248Numerators := by
  intro i
  fin_cases i <;> norm_num [adoptedH248Numerators]

theorem adopted_H248_data_bounds : UnitBoundedData H248Numerators :=
  P5Z.U11H248.H248_numerator_bounds

theorem adoptedHnew_bounds (s : ℝ) : 0 ≤ adoptedHnew s ∧ adoptedHnew s ≤ Real.log 5 :=
  tableTail_bounds_of_data adopted_h248_data_bounds _

theorem adoptedhnew_bounds (s : ℝ) : 0 ≤ adoptedhnew s ∧ adoptedhnew s ≤ Real.log 5 :=
  tableTail_bounds_of_data adopted_H248_data_bounds _

/-- Explicit exact coefficient/log formulas for the two actual input arrays. -/
theorem adoptedHnew_eq_finite_log (s : ℝ) :
    adoptedHnew s = ∑ i : Fin 200, floorValue adoptedH248Numerators i *
      Real.log (floorGrid (i.val + 1) / clippedCellLeft i (max 2 (s - 1))) :=
  tableTail_eq_finite_log _ _

theorem adoptedhnew_eq_finite_log (s : ℝ) :
    adoptedhnew s = ∑ i : Fin 200, floorValue H248Numerators i *
      Real.log (floorGrid (i.val + 1) / clippedCellLeft i (s - 1)) :=
  tableTail_eq_finite_log _ _

end
end ImbalancedChen.Part5UpperTables.Renewal
