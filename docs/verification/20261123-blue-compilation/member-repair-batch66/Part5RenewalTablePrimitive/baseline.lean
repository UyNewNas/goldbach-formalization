import ImbalancedChen.Part5UpperTableLookup

/-!
Exact positive renewal primitives of the actual finite tables. SOURCE ONLY.
This file proves stored-table integral semantics, not H/h count semantics.
P2TableActionSoundness has rounded lower enclosures against Wu source
functions; it does not supply these exact clipped-log stored-table identities.
-/

namespace ImbalancedChen.Part5UpperTables.Renewal

noncomputable section

open Set MeasureTheory Filter
open scoped BigOperators Interval
open Part5OriginalUpsilon5CausalDictionary

def halfOpenTable (nums : Fin 200 → ℤ) (w : ℝ) : ℝ :=
  ∑ i : Fin 200, (Ico (floorGrid i.val) (floorGrid (i.val + 1))).indicator
    (fun _ => floorValue nums i) w

theorem grid_bounds {j : ℕ} (hj : j ≤ 200) : 1 ≤ floorGrid j ∧ floorGrid j ≤ 5 := by
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hjr : (j : ℝ) ≤ 200 := by exact_mod_cast hj
  dsimp [floorGrid]
  constructor <;> linarith

theorem grid_mono {i j : ℕ} (hij : i ≤ j) : floorGrid i ≤ floorGrid j := by
  have h : (i : ℝ) ≤ j := by exact_mod_cast hij
  dsimp [floorGrid]
  linarith

/-- The true scalar seam values disappear only after proving their scalar nullity. -/
theorem upperFloor_eq_halfOpen_away_knots (nums : Fin 200 → ℤ) (w : ℝ)
    (hne : ∀ j : Fin 201, w ≠ floorGrid j.val) :
    upperFloor nums w = halfOpenTable nums w := by
  have hk : (∑ j : Fin 201,
      (upperAtomSet (Sum.inr j)).indicator (fun _ => floorAtomValue nums (Sum.inr j)) w) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    exact indicator_of_notMem (fun hj => hne j hj.2) _
  have hc : (∑ i : Fin 200,
      (upperAtomSet (Sum.inl i)).indicator (fun _ => floorAtomValue nums (Sum.inl i)) w) =
        halfOpenTable nums w := by
    apply Finset.sum_congr rfl
    intro i _
    have hlo := (grid_bounds (show i.val ≤ 200 by omega)).1
    have hhi := (grid_bounds (show i.val + 1 ≤ 200 by omega)).2
    have hneq : w ≠ floorGrid i.val := hne i.castSucc
    have heq : w ∈ upperAtomSet (Sum.inl i) ↔
        w ∈ Ico (floorGrid i.val) (floorGrid (i.val + 1)) := by
      change (w ∈ Icc (1 : ℝ) 5 ∧ floorGrid i.val < w ∧
        w < floorGrid (i.val + 1)) ↔ _
      constructor
      · exact fun hw => ⟨hw.2.1.le, hw.2.2⟩
      · intro hw
        exact ⟨⟨hlo.trans hw.1, hw.2.le.trans hhi⟩,
          lt_of_le_of_ne hw.1 (Ne.symm hneq), hw.2⟩
    by_cases hi : w ∈ Ico (floorGrid i.val) (floorGrid (i.val + 1))
    · rw [indicator_of_mem (heq.mpr hi), indicator_of_mem hi]
      rfl
    · rw [indicator_of_notMem (fun hw => hi (heq.mp hw)), indicator_of_notMem hi]
  unfold upperFloor
  rw [Fintype.sum_sum_type, hk, add_zero]
  exact hc

theorem ae_ne_all_scalar_knots :
    ∀ᵐ w : ℝ ∂volume, ∀ j : Fin 201, w ≠ floorGrid j.val := by
  apply ae_all_iff.mpr
  intro j
  rw [ae_iff]
  simpa only [not_not] using (measure_singleton (floorGrid j.val) :
    volume {floorGrid j.val} = 0)

theorem upperFloor_ae_eq_halfOpen (nums : Fin 200 → ℤ) :
    upperFloor nums =ᵐ[volume] halfOpenTable nums := by
  filter_upwards [ae_ne_all_scalar_knots] with w hw
  exact upperFloor_eq_halfOpen_away_knots nums w hw

theorem halfOpen_div_eq_sum (nums : Fin 200 → ℤ) (w : ℝ) :
    halfOpenTable nums w / w = ∑ i : Fin 200, floorValue nums i *
      (Ico (floorGrid i.val) (floorGrid (i.val + 1))).indicator (fun z : ℝ => 1 / z) w := by
  unfold halfOpenTable
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : w ∈ Ico (floorGrid i.val) (floorGrid (i.val + 1)) <;>
    simp [hi, div_eq_mul_inv]

theorem integrableOn_upperFloor_div (nums : Fin 200 → ℤ) :
    IntegrableOn (fun w => upperFloor nums w / w) (Icc (1 : ℝ) 5) := by
  have hw : IntegrableOn (fun w : ℝ => 1 / w) (Icc (1 : ℝ) 5) := by
    exact (continuousOn_const.div continuousOn_id
      (fun w hw => (lt_of_lt_of_le (by norm_num) hw.1).ne')).integrableOn_compact isCompact_Icc
  have hi : IntegrableOn (fun w : ℝ => ∑ i : Fin 200, floorValue nums i *
      (Ico (floorGrid i.val) (floorGrid (i.val + 1))).indicator (fun z : ℝ => 1 / z) w)
      (Icc (1 : ℝ) 5) :=
    integrable_finsetSum _ (fun i _ => (hw.indicator measurableSet_Ico).const_mul _)
  apply hi.congr
  filter_upwards [ae_restrict_of_ae (upperFloor_ae_eq_halfOpen nums)] with w heq
  rw [heq, halfOpen_div_eq_sum]

/-- The true weighted step function is globally integrable, including its exterior zero part. -/
theorem integrable_upperFloor_div (nums : Fin 200 → ℤ) :
    Integrable (fun w : ℝ => upperFloor nums w / w) := by
  have hi := (integrableOn_upperFloor_div nums).integrable_indicator measurableSet_Icc
  apply hi.congr
  apply Filter.Eventually.of_forall
  intro w
  by_cases hw : w ∈ Icc (1 : ℝ) 5
  · rw [indicator_of_mem hw]
  · rw [indicator_of_notMem hw, upperFloor_outside nums hw, zero_div]

theorem intervalIntegrable_upperFloor_div (nums : Fin 200 → ℤ) (c d : ℝ) :
    IntervalIntegrable (fun w => upperFloor nums w / w) volume c d :=
  (integrable_upperFloor_div nums).intervalIntegrable

def tailDomain (c : ℝ) : Set ℝ := Ico (max 1 c) 5
def tableTail (nums : Fin 200 → ℤ) (c : ℝ) : ℝ :=
  ∫ w in tailDomain c, upperFloor nums w / w

theorem tailDomain_subset (c : ℝ) : tailDomain c ⊆ Icc (1 : ℝ) 5 := by
  intro w hw
  exact ⟨(le_max_left _ _).trans hw.1, hw.2.le⟩

theorem integrableOn_tableTail (nums : Fin 200 → ℤ) (c : ℝ) :
    IntegrableOn (fun w => upperFloor nums w / w) (tailDomain c) :=
  (integrableOn_upperFloor_div nums).mono_set (tailDomain_subset c)

theorem tableTail_zero_of_five_le (nums : Fin 200 → ℤ) {c : ℝ} (hc : 5 ≤ c) :
    tableTail nums c = 0 := by
  unfold tableTail tailDomain
  have he : Ico (max (1 : ℝ) c) 5 = ∅ :=
    Ico_eq_empty_of_le (hc.trans (le_max_right _ _))
  rw [he, setIntegral_empty]

/-- Also the literal oriented integral, including the zero tail beyond five. -/
theorem tableTail_eq_interval (nums : Fin 200 → ℤ) {c : ℝ} (hc : 1 ≤ c) :
    tableTail nums c = ∫ w in c..5, upperFloor nums w / w := by
  by_cases hc5 : c ≤ 5
  · unfold tableTail tailDomain
    rw [max_eq_right hc, integral_Ico_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le hc5]
  · have h5c : 5 ≤ c := le_of_not_ge hc5
    rw [tableTail_zero_of_five_le nums h5c, intervalIntegral.integral_of_ge h5c]
    have hz : (∫ w in Ioc (5 : ℝ) c, upperFloor nums w / w) = 0 := by
      calc
        _ = ∫ _w in Ioc (5 : ℝ) c, (0 : ℝ) := by
          apply setIntegral_congr_fun measurableSet_Ioc
          intro w hw
          rw [upperFloor_outside nums (show w ∉ Icc (1 : ℝ) 5 from
            fun h => (not_lt_of_ge h.2) hw.1), zero_div]
        _ = 0 := by simp
    rw [hz, neg_zero]

def clippedCellLeft (i : Fin 200) (c : ℝ) : ℝ :=
  min (floorGrid (i.val + 1)) (max c (floorGrid i.val))

theorem clippedCellLeft_bounds (i : Fin 200) (c : ℝ) :
    1 ≤ clippedCellLeft i c ∧ clippedCellLeft i c ≤ floorGrid (i.val + 1) := by
  have hlo := (grid_bounds (show i.val ≤ 200 by omega)).1
  have hhi := (grid_bounds (show i.val + 1 ≤ 200 by omega)).1
  exact ⟨le_min hhi (hlo.trans (le_max_right _ _)), min_le_left _ _⟩

theorem tail_cell_intersection (i : Fin 200) (c : ℝ) :
    tailDomain c ∩ Ico (floorGrid i.val) (floorGrid (i.val + 1)) =
      Ico (clippedCellLeft i c) (floorGrid (i.val + 1)) := by
  have hlo := (grid_bounds (show i.val ≤ 200 by omega)).1
  have hhi := (grid_bounds (show i.val + 1 ≤ 200 by omega)).2
  have heq : tailDomain c ∩ Ico (floorGrid i.val) (floorGrid (i.val + 1)) =
      Ico (max c (floorGrid i.val)) (floorGrid (i.val + 1)) := by
    ext w
    simp only [tailDomain, mem_inter_iff, mem_Ico, max_le_iff]
    constructor
    · rintro ⟨⟨⟨_, hc⟩, _⟩, hlo', hhi'⟩
      exact ⟨⟨hc, hlo'⟩, hhi'⟩
    · rintro ⟨⟨hc, hlo'⟩, hhi'⟩
      exact ⟨⟨⟨hlo.trans hlo', hc⟩, hhi'.trans_le hhi⟩, hlo', hhi'⟩
  rw [heq]
  unfold clippedCellLeft
  by_cases hh : max c (floorGrid i.val) ≤ floorGrid (i.val + 1)
  · rw [min_eq_right hh]
  · have hh' : floorGrid (i.val + 1) ≤ max c (floorGrid i.val) := le_of_not_ge hh
    ext w
    simp only [mem_Ico, min_eq_left hh']
    constructor <;> rintro ⟨hw1, hw2⟩ <;> linarith

theorem tail_cell_log (i : Fin 200) (c : ℝ) :
    (∫ w in tailDomain c ∩ Ico (floorGrid i.val) (floorGrid (i.val + 1)), 1 / w) =
      Real.log (floorGrid (i.val + 1) / clippedCellLeft i c) := by
  rw [tail_cell_intersection]
  exact integral_one_div_Ico (lt_of_lt_of_le (by norm_num) (clippedCellLeft_bounds i c).1)
    (clippedCellLeft_bounds i c).2

/-- Exact real primitive, suitable for independent rational log enclosures. -/
theorem tableTail_eq_finite_log (nums : Fin 200 → ℤ) (c : ℝ) :
    tableTail nums c = ∑ i : Fin 200, floorValue nums i *
      Real.log (floorGrid (i.val + 1) / clippedCellLeft i c) := by
  have hw : IntegrableOn (fun w : ℝ => 1 / w) (tailDomain c) := by
    exact ((continuousOn_const.div continuousOn_id
      (fun w hw => (lt_of_lt_of_le (by norm_num) hw.1).ne')).integrableOn_compact
        isCompact_Icc).mono_set (tailDomain_subset c)
  unfold tableTail
  calc
    _ = ∫ w in tailDomain c, halfOpenTable nums w / w := by
      apply setIntegral_congr_ae measurableSet_Ico
      filter_upwards [upperFloor_ae_eq_halfOpen nums] with w heq
      intro _
      rw [heq]
    _ = ∫ w in tailDomain c, ∑ i : Fin 200, floorValue nums i *
        (Ico (floorGrid i.val) (floorGrid (i.val + 1))).indicator (fun z : ℝ => 1 / z) w := by
      apply setIntegral_congr_fun measurableSet_Ico
      intro w _
      exact halfOpen_div_eq_sum nums w
    _ = ∑ i : Fin 200, ∫ w in tailDomain c, floorValue nums i *
        (Ico (floorGrid i.val) (floorGrid (i.val + 1))).indicator (fun z : ℝ => 1 / z) w :=
      integral_finsetSum _ (fun i _ => (hw.indicator measurableSet_Ico).const_mul _)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [integral_const_mul, setIntegral_indicator measurableSet_Ico, tail_cell_log]

theorem continuous_clippedCellLeft (i : Fin 200) : Continuous (clippedCellLeft i) :=
  continuous_const.min (continuous_id.max continuous_const)

theorem continuous_tableTail (nums : Fin 200 → ℤ) : Continuous (tableTail nums) := by
  have hformula : tableTail nums = fun c => ∑ i : Fin 200, floorValue nums i *
      Real.log (floorGrid (i.val + 1) / clippedCellLeft i c) := by
    funext c
    exact tableTail_eq_finite_log nums c
  rw [hformula]
  apply continuous_finsetSum
  intro i _
  apply continuous_const.mul
  apply Continuous.log
  · exact continuous_const.div (continuous_clippedCellLeft i)
      (fun c => (lt_of_lt_of_le (by norm_num) (clippedCellLeft_bounds i c).1).ne')
  · intro c
    exact div_ne_zero
      (lt_of_lt_of_le (by norm_num) (grid_bounds (show i.val + 1 ≤ 200 by omega)).1).ne'
      (lt_of_lt_of_le (by norm_num) (clippedCellLeft_bounds i c).1).ne'

def upperTransition (lowerNums : Fin 200 → ℤ) (s : ℝ) : ℝ :=
  tableTail lowerNums (max 2 (s - 1))

def lowerTransition (upperNums : Fin 200 → ℤ) (s : ℝ) : ℝ := tableTail upperNums (s - 1)

theorem continuous_upperTransition (nums : Fin 200 → ℤ) : Continuous (upperTransition nums) :=
  (continuous_tableTail nums).comp (continuous_const.max (continuous_id.sub continuous_const))

theorem continuous_lowerTransition (nums : Fin 200 → ℤ) : Continuous (lowerTransition nums) :=
  (continuous_tableTail nums).comp (continuous_id.sub continuous_const)

theorem upperTransition_literal (nums : Fin 200 → ℤ) (s : ℝ) :
    upperTransition nums s =
      ∫ w in Ico (max 2 (s - 1)) 5, floorStep nums w / w := by
  have hstart : max 1 (max 2 (s - 1)) = max 2 (s - 1) :=
    max_eq_right (by linarith [le_max_left (2 : ℝ) (s - 1)])
  unfold upperTransition tableTail tailDomain
  rw [hstart]
  apply setIntegral_congr_fun measurableSet_Ico
  intro w hw
  rw [upperFloor_eq_lowerFloor_of_two_le nums
    ((le_max_left (2 : ℝ) (s - 1)).trans hw.1)]

theorem lowerTransition_literal (nums : Fin 200 → ℤ) {s : ℝ} (hs : 2 ≤ s) :
    lowerTransition nums s = ∫ w in Ico (s - 1) 5, upperFloor nums w / w := by
  unfold lowerTransition tableTail tailDomain
  rw [max_eq_right (by linarith : (1 : ℝ) ≤ s - 1)]

theorem upperTransition_eq_interval_raw (nums : Fin 200 → ℤ) (s : ℝ) :
    upperTransition nums s =
      ∫ w in (max 2 (s - 1))..5, upperFloor nums w / w :=
  tableTail_eq_interval nums (by linarith [le_max_left (2 : ℝ) (s - 1)])

theorem lowerTransition_eq_interval (nums : Fin 200 → ℤ) {s : ℝ} (hs : 2 ≤ s) :
    lowerTransition nums s = ∫ w in (s - 1)..5, upperFloor nums w / w :=
  tableTail_eq_interval nums (by linarith)

def adoptedHnew : ℝ → ℝ := upperTransition adoptedH248Numerators
def adoptedhnew : ℝ → ℝ := lowerTransition H248Numerators

theorem continuous_adoptedHnew : Continuous adoptedHnew := continuous_upperTransition _
theorem continuous_adoptedhnew : Continuous adoptedhnew := continuous_lowerTransition _

theorem adoptedHnew_literal (s : ℝ) :
    adoptedHnew s = ∫ w in Ico (max 2 (s - 1)) 5, adoptedH248Floor w / w :=
  upperTransition_literal _ _

theorem adoptedhnew_literal {s : ℝ} (hs : 2 ≤ s) :
    adoptedhnew s = ∫ w in Ico (s - 1) 5, H248 w / w :=
  lowerTransition_literal _ hs

theorem adoptedhnew_interval {s : ℝ} (hs : 2 ≤ s) :
    adoptedhnew s = ∫ w in (s - 1)..5, H248 w / w :=
  lowerTransition_eq_interval _ hs

end
end ImbalancedChen.Part5UpperTables.Renewal
