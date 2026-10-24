import ImbalancedChen.Part5OriginalUpsilon5CausalSplit
import ImbalancedChen.Part5AdoptedH248Data

/-!
The adopted finite h248 floor as a bounded measurable function. SOURCE ONLY.

SavedDefects.lookup in certify_combined_chen_functional.py takes the minimum
of all CLOSED grid cells meeting its argument enclosure, including BOTH
neighbors at a knot. At scalar arguments this gives an open-cell value and
the adjacent minimum at internal knots. There is no interpolation in that
lookup. Lower lookup outside [2,5] is zero. The explicit finite atom form
below preserves the singleton values, even if a pullback knot had mass.

The 200 adopted integers are serialized data, not proved recurrence outputs.
All analytic conclusions here hold for EVERY integer array. No finite-table
feedback bound or h248 averaged count semantics is asserted.
-/

namespace ImbalancedChen.Part5OriginalUpsilon5CausalDictionary

noncomputable section

open MeasureTheory Set
open scoped BigOperators

abbrev FloorAtom := Fin 200 ⊕ Fin 201

def floorGrid (j : ℕ) : ℝ := 1 + (j : ℝ) / 50
def floorValue (nums : Fin 200 → ℤ) (i : Fin 200) : ℝ := (nums i : ℝ) / (2 ^ 80 : ℝ)

/-- At an interior knot both closed neighbors participate in the lookup. -/
def floorKnotValue (nums : Fin 200 → ℤ) (j : Fin 201) : ℝ :=
  if h0 : j.val = 0 then floorValue nums 0
  else if hlast : j.val = 200 then floorValue nums 199
  else min (floorValue nums ⟨j.val - 1, by omega⟩)
    (floorValue nums ⟨j.val, by omega⟩)

def floorAtomValue (nums : Fin 200 → ℤ) : FloorAtom → ℝ
  | .inl i => floorValue nums i
  | .inr j => floorKnotValue nums j

/-- Open cells and separate knot singletons retain the literal closed-cell floor. -/
def floorAtomSet : FloorAtom → Set ℝ
  | .inl i => Icc 2 5 ∩ Ioo (floorGrid i.val) (floorGrid (i.val + 1))
  | .inr j => Icc 2 5 ∩ {floorGrid j.val}

theorem measurableSet_floorAtomSet (b : FloorAtom) : MeasurableSet (floorAtomSet b) := by
  cases b with
  | inl i => exact measurableSet_Icc.inter measurableSet_Ioo
  | inr j => exact measurableSet_Icc.inter (measurableSet_singleton _)

def floorStep (nums : Fin 200 → ℤ) (s : ℝ) : ℝ :=
  ∑ b : FloorAtom, (floorAtomSet b).indicator (fun _ => floorAtomValue nums b) s

def floorBound (nums : Fin 200 → ℤ) : ℝ := ∑ b : FloorAtom, ‖floorAtomValue nums b‖

theorem floor_atom_count : Fintype.card FloorAtom = 401 := by norm_num [FloorAtom]

theorem measurable_floorStep (nums : Fin 200 → ℤ) : Measurable (floorStep nums) := by
  apply Finset.measurable_sum
  intro b _
  exact measurable_const.indicator (measurableSet_floorAtomSet b)

theorem floorStep_outside (nums : Fin 200 → ℤ) {s : ℝ} (hs : s ∉ Icc (2 : ℝ) 5) :
    floorStep nums s = 0 := by
  apply Finset.sum_eq_zero
  intro b _
  have hb : s ∉ floorAtomSet b := by cases b <;> exact fun h => hs h.1
  exact indicator_of_notMem hb _

/-- Automatic global finite bound, including endpoints and signed arrays. -/
theorem norm_floorStep_le (nums : Fin 200 → ℤ) (s : ℝ) :
    ‖floorStep nums s‖ ≤ floorBound nums := by
  unfold floorStep floorBound
  calc
    ‖∑ b : FloorAtom, (floorAtomSet b).indicator (fun _ => floorAtomValue nums b) s‖ ≤
        ∑ b : FloorAtom, ‖(floorAtomSet b).indicator (fun _ => floorAtomValue nums b) s‖ :=
      norm_sum_le _ _
    _ ≤ ∑ b : FloorAtom, ‖floorAtomValue nums b‖ := by
      apply Finset.sum_le_sum
      intro b _
      by_cases hb : s ∈ floorAtomSet b
      · simp only [indicator_of_mem hb]
        exact le_rfl
      · simp only [indicator_of_notMem hb, norm_zero]
        exact norm_nonneg _

theorem floorBound_nonneg (nums : Fin 200 → ℤ) : 0 ≤ floorBound nums :=
  Finset.sum_nonneg (fun _ _ => norm_nonneg _)

def pulledFloorAtom (b : FloorAtom) : Set (Fin 2 → ℝ) := argument ⁻¹' floorAtomSet b

theorem measurableSet_pulledFloorAtom (b : FloorAtom) : MeasurableSet (pulledFloorAtom b) :=
  (measurableSet_floorAtomSet b).preimage continuous_argument.measurable

/-- The exact positive denominator weight used by every correction atom. -/
def correctionWeight (x : Fin 2 → ℝ) : ℝ := (4 / residual x) * ∏ i, 1 / x i

theorem continuousOn_correctionWeight_closedTriangle :
    ContinuousOn correctionWeight closedTriangle := by
  apply (continuousOn_const.div continuous_residual.continuousOn
    (fun _ hx => (closedTriangle_bounds hx).1.ne')).mul
  apply continuousOn_finsetProd
  intro i _
  apply continuousOn_const.div (continuous_apply i).continuousOn
  intro x hx
  exact (lt_of_lt_of_le (by norm_num [a] : 0 < a)
    (hx.1 i (mem_univ _)).1).ne'

theorem integrableOn_correctionWeight : IntegrableOn correctionWeight triangle :=
  (continuousOn_correctionWeight_closedTriangle.integrableOn_compact
    isCompact_closedTriangle).mono_set triangle_subset_closedTriangle

/-- Every denominator retains the fixed positive margins from the original domain. -/
theorem original_denominator_margins {x : Fin 2 → ℝ} (hx : x ∈ triangle) :
    (34 / 125 : ℝ) ≤ residual x ∧ a ≤ x 0 ∧ a ≤ x 1 := by
  obtain ⟨hu, hut, ht⟩ := mem_triangle.mp hx
  exact ⟨(residual_bounds hu hut.le ht.le).1, hu, hu.trans hut.le⟩

def atomCorrection (nums : Fin 200 → ℤ) (b : FloorAtom) (x : Fin 2 → ℝ) : ℝ :=
  floorAtomValue nums b * (pulledFloorAtom b).indicator correctionWeight x

theorem correction_eq_finite_sum (nums : Fin 200 → ℤ) (x : Fin 2 → ℝ) :
    floorStep nums (argument x) * correctionWeight x =
      ∑ b : FloorAtom, atomCorrection nums b x := by
  unfold floorStep
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro b _
  by_cases hb : argument x ∈ floorAtomSet b
  · simp [atomCorrection, pulledFloorAtom, hb]
  · simp [atomCorrection, pulledFloorAtom, hb]

theorem integrableOn_atomCorrection (nums : Fin 200 → ℤ) (b : FloorAtom) :
    IntegrableOn (atomCorrection nums b) triangle :=
  (integrableOn_correctionWeight.indicator (measurableSet_pulledFloorAtom b)).const_mul _

theorem integrableOn_floorCorrection (nums : Fin 200 → ℤ) :
    IntegrableOn (fun x => floorStep nums (argument x) * correctionWeight x) triangle := by
  have hi : IntegrableOn (fun x => ∑ b : FloorAtom, atomCorrection nums b x) triangle :=
    integrable_finsetSum _ (fun b _ => integrableOn_atomCorrection nums b)
  apply hi.congr_fun ?_ measurableSet_triangle
  intro x _
  exact (correction_eq_finite_sum nums x).symm

theorem weightedKernel_eq_base_add_floor (nums : Fin 200 → ℤ) (x : Fin 2 → ℝ) :
    kernel (floorStep nums) x * (∏ i, 1 / x i) =
      kernel (fun _ => 0) x * (∏ i, 1 / x i) +
        floorStep nums (argument x) * correctionWeight x := by
  dsimp [kernel, correctionWeight]
  ring

/-- No continuity, positivity or semantic soundness premise on the finite array. -/
theorem integrableOn_floorKernel (nums : Fin 200 → ℤ) :
    IntegrableOn (fun x => kernel (floorStep nums) x * ∏ i, 1 / x i) triangle := by
  have hi := (integrableOn_weightedKernel (fun _ => 0) continuousOn_const).add
    (integrableOn_floorCorrection nums)
  apply hi.congr_fun ?_ measurableSet_triangle
  intro x _
  exact (weightedKernel_eq_base_add_floor nums x).symm

/-- Exact finite-table Fubini: real integrals over every cell AND knot pullback.
No boundary piece is discarded and no table value is treated as a recurrence proof. -/
theorem integral_floor_finite_fubini (nums : Fin 200 → ℤ) :
    integral (floorStep nums) = integral (fun _ => 0) +
      ∑ b : FloorAtom, floorAtomValue nums b *
        ∫ x in triangle ∩ pulledFloorAtom b, correctionWeight x := by
  unfold integral
  calc
    _ = ∫ x in triangle,
        kernel (fun _ => 0) x * (∏ i, 1 / x i) +
          floorStep nums (argument x) * correctionWeight x := by
      apply setIntegral_congr_fun measurableSet_triangle
      intro x _
      exact weightedKernel_eq_base_add_floor nums x
    _ = (∫ x in triangle, kernel (fun _ => 0) x * (∏ i, 1 / x i)) +
        ∫ x in triangle, floorStep nums (argument x) * correctionWeight x :=
      integral_add (integrableOn_weightedKernel (fun _ => 0) continuousOn_const)
        (integrableOn_floorCorrection nums)
    _ = _ := by
      congr 1
      calc
        _ = ∫ x in triangle, ∑ b : FloorAtom, atomCorrection nums b x := by
          apply setIntegral_congr_fun measurableSet_triangle
          intro x _
          exact correction_eq_finite_sum nums x
        _ = ∑ b : FloorAtom, ∫ x in triangle, atomCorrection nums b x :=
          integral_finsetSum _ (fun b _ => integrableOn_atomCorrection nums b)
        _ = _ := by
          apply Finset.sum_congr rfl
          intro b _
          simp only [atomCorrection]
          rw [integral_const_mul, setIntegral_indicator (measurableSet_pulledFloorAtom b)]

/-- Genuine two-coordinate Fubini for each individual table piece.
The indicator retains the exact enhanced max-level region and knot convention. -/
theorem floorAtom_integral_nested (b : FloorAtom) :
    (∫ x in triangle ∩ pulledFloorAtom b, correctionWeight x) =
      ∫ u : ℝ, ∫ t : ℝ,
        (triangle ∩ pulledFloorAtom b).indicator correctionWeight ![u, t] := by
  let S := triangle ∩ pulledFloorAtom b
  let F := S.indicator correctionWeight
  have hS : MeasurableSet S :=
    measurableSet_triangle.inter (measurableSet_pulledFloorAtom b)
  have hF : Integrable F :=
    (integrableOn_correctionWeight.mono_set inter_subset_left).integrable_indicator hS
  let E := MeasurableEquiv.piFinTwo (fun _ : Fin 2 => ℝ)
  have hE : MeasurePreserving E := volume_preserving_piFinTwo _
  have hPF : Integrable (fun p : ℝ × ℝ => F (E.symm p)) :=
    (hE.symm.integrable_comp_emb E.symm.measurableEmbedding).mpr hF
  have hvec (u t : ℝ) : E.symm (u, t) = ![u, t] := by
    ext i
    fin_cases i <;> rfl
  calc
    _ = ∫ x, F x := (integral_indicator hS).symm
    _ = ∫ p : ℝ × ℝ, F (E.symm p) := (hE.symm.integral_comp' F).symm
    _ = ∫ u : ℝ, ∫ t : ℝ, F (E.symm (u, t)) := integral_prod _ hPF
    _ = _ := by simp only [hvec]

theorem integral_floor_nested_fubini (nums : Fin 200 → ℤ) :
    integral (floorStep nums) = integral (fun _ => 0) +
      ∑ b : FloorAtom, floorAtomValue nums b *
        ∫ u : ℝ, ∫ t : ℝ,
          (triangle ∩ pulledFloorAtom b).indicator correctionWeight ![u, t] := by
  rw [integral_floor_finite_fubini]
  congr 1
  apply Finset.sum_congr rfl
  intro b _
  rw [floorAtom_integral_nested]

/-- The earlier exact split now applies to every finite floor without a continuity premise. -/
theorem integral_floor_split_log_canonical (nums : Fin 200 → ℤ) :
    integral (floorStep nums) =
      (∫ x in firstRegion,
        (4 * (Real.log (argument x - 1) + floorStep nums (argument x)) / residual x) *
          ∏ i, 1 / x i) +
      ∫ x in secondRegion, canonicalKernel (floorStep nums) x * ∏ i, 1 / x i := by
  have hi := integrableOn_floorKernel nums
  have hsplit : integral (floorStep nums) =
      (∫ x in firstRegion, kernel (floorStep nums) x * ∏ i, 1 / x i) +
        ∫ x in secondRegion, kernel (floorStep nums) x * ∏ i, 1 / x i := by
    unfold integral
    rw [← regions_union]
    exact setIntegral_union regions_disjoint measurableSet_secondRegion
      (hi.mono_set inter_subset_left) (hi.mono_set inter_subset_left)
  rw [hsplit]
  congr 1
  · apply setIntegral_congr_fun measurableSet_firstRegion
    intro x hx
    rw [kernel_eq_log_of_argument_le_four hx.1 hx.2]
  · apply setIntegral_congr_fun measurableSet_secondRegion
    intro x hx
    rw [kernel_eq_canonical hx.1]

def adoptedH248Floor : ℝ → ℝ := floorStep adoptedH248Numerators

theorem measurable_adoptedH248Floor : Measurable adoptedH248Floor :=
  measurable_floorStep _

theorem norm_adoptedH248Floor_le (s : ℝ) :
    ‖adoptedH248Floor s‖ ≤ floorBound adoptedH248Numerators := norm_floorStep_le _ _

theorem integrableOn_adoptedH248Kernel :
    IntegrableOn (fun x => kernel adoptedH248Floor x * ∏ i, 1 / x i) triangle :=
  integrableOn_floorKernel _

theorem adoptedH248_integral_finite_fubini :
    integral adoptedH248Floor = integral (fun _ => 0) +
      ∑ b : FloorAtom, floorAtomValue adoptedH248Numerators b *
        ∫ x in triangle ∩ pulledFloorAtom b, correctionWeight x :=
  integral_floor_finite_fubini _

end

end ImbalancedChen.Part5OriginalUpsilon5CausalDictionary
