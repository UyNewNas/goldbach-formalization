import ImbalancedChen.P3OriginalU5WarmAdmissionView

/-!
# Actual word coordinates and half-open coarse boundaries

SOURCE ONLY / UNCOMPILED / NO FORMAL ACCEPTANCE.

The point bounds call the existing same-floor-word lemma on singleton
lists. The affine cube row is the exact reused row, not a new sieve gate.
Coarse disagreement includes values outside the receiver interval: the
actual `none` code is used exactly as defined, including both endpoints.
-/

namespace ImbalancedChen.P3OriginalU5WarmWordWalls

noncomputable section
open scoped Classical BigOperators List
open P2PhysicalIncomingPrefixCells P2LowerCapPlanIntegerRetention
open P3OriginalU5WarmCapCodeStability

def wordPoint (r : ℕ) (xs : List ℝ) : Fin r → ℝ :=
  fun i => xs.getD i.val 0

theorem wordPoint_getElem {r : ℕ} (xs : List ℝ) (hx : xs.length = r)
    (i : Fin r) : wordPoint r xs i = getElem xs i.val (by omega) := by
  exact (List.getElem_eq_getD (h := by omega) 0).symm

theorem ofFn_wordPoint {r : ℕ} (xs : List ℝ) (hx : xs.length = r) :
    List.ofFn (wordPoint r xs) = xs := by
  apply List.ext_getElem
  · simpa only [List.length_ofFn] using hx.symm
  · intro i hi hi'
    simp only [List.getElem_ofFn]
    exact wordPoint_getElem xs hx ⟨i, by simpa only [List.length_ofFn] using hi⟩

theorem cubeRow_wordPoint {r : ℕ} (xs : List ℝ) (hx : xs.length = r)
    (i : Fin r) :
    P5Z.PresievedRoughSlotAffineGates.cubeRow i (wordPoint r xs) =
      (xs.take i.val).sum + 3 * getElem xs i.val (by omega) := by
  rw [P5Z.PresievedRoughSlotAffineGates.cubeRow_apply]
  unfold P5Z.PresievedRoughSlotAffineGates.cube P5Z.PresievedRoughSlotAffineGates.«prefix»
  have hsum : (xs.take i.val).sum =
      ∑ j : Fin r with j.val < i.val, wordPoint r xs j := by
    simpa only [ofFn_wordPoint xs hx] using List.sum_take_ofFn (wordPoint r xs) i.val
  rw [← hsum, wordPoint_getElem xs hx]

theorem same_floor_coordinate_le {tau : ℝ} (htau : 0 < tau)
    (xs ys : List ℝ)
    (hxy : xs.map (fun x => (⌊x / tau⌋ : ℤ)) =
      ys.map (fun y => (⌊y / tau⌋ : ℤ)))
    (i : ℕ) (hi : i < xs.length) :
    |xs[i] - getElem ys i (by
      have hlen : xs.length = ys.length := by
        simpa only [List.length_map] using congrArg List.length hxy
      omega)| ≤ tau := by
  have hlen : xs.length = ys.length := by
    simpa only [List.length_map] using congrArg List.length hxy
  have hf : (⌊xs[i] / tau⌋ : ℤ) = ⌊getElem ys i (by omega) / tau⌋ := by
    simpa only [List.getElem_map] using
      List.getElem_of_eq hxy (show i < (xs.map (fun x => (⌊x / tau⌋ : ℤ))).length by
        simpa only [List.length_map] using hi)
  have hsingle : [xs[i]].map (fun x => (⌊x / tau⌋ : ℤ)) =
      [getElem ys i (by omega)].map (fun y => (⌊y / tau⌋ : ℤ)) := by
    simpa only [List.map_cons, List.map_nil] using congrArg (fun z : ℤ => [z]) hf
  have hforward := P2RoundedCausalFibreLossAndLevel.same_floor_word_sum_le
    htau [xs[i]] [getElem ys i (by omega)] hsingle
  have hbackward := P2RoundedCausalFibreLossAndLevel.same_floor_word_sum_le
    htau [getElem ys i (by omega)] [xs[i]] hsingle.symm
  simp only [List.sum_cons, List.sum_nil, add_zero, List.length_singleton,
    Nat.cast_one, one_mul] at hforward hbackward
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem same_floor_wordPoint_norm_le {tau : ℝ} (htau : 0 < tau)
    {r : ℕ} (xs ys : List ℝ) (hx : xs.length = r) (hy : ys.length = r)
    (hxy : xs.map (fun x => (⌊x / tau⌋ : ℤ)) =
      ys.map (fun y => (⌊y / tau⌋ : ℤ))) :
    ‖wordPoint r xs - wordPoint r ys‖ ≤ tau := by
  apply (pi_norm_le_iff_of_nonneg htau.le).mpr
  intro i
  simpa only [Pi.sub_apply, Real.norm_eq_abs, wordPoint_getElem xs hx,
    wordPoint_getElem ys hy] using
      same_floor_coordinate_le htau xs ys hxy i.val (by omega)

private theorem exponentCode_some_membership {a b : ℝ} {mesh : ℕ} {x : ℝ}
    {j : Fin (mesh + 1)} (hj : exponentCode a b mesh x = some j) :
    x ∈ Set.Ico (logPrimeMeshPoint a b mesh j.val)
      (logPrimeMeshPoint a b mesh (j.val + 1)) := by
  unfold exponentCode at hj
  split_ifs at hj with hx
  · have he := Option.some.inj hj
    simpa only [he] using Classical.choose_spec (exists_logPrimeMeshInterval a b mesh hx)
  · cases hj

private theorem exponentCode_eq_of_mesh_interval {a b : ℝ} (hab : a < b)
    {mesh : ℕ} {x : ℝ} (j : Fin (mesh + 1))
    (hx : x ∈ Set.Ico (logPrimeMeshPoint a b mesh j.val)
      (logPrimeMeshPoint a b mesh (j.val + 1))) :
    exponentCode a b mesh x = some j := by
  have hb := logPrimeMeshLoHi_bounds (d := 1) hab mesh (fun _ => j) 0
  have hxab : x ∈ Set.Icc a b :=
    ⟨hb.1.trans hx.1, hx.2.le.trans hb.2.2⟩
  exact exponentCode_eq_of_cell hab hxab hx

/-- A half-open ownership change is charged at x, on either side of a wall. -/
private theorem interval_disagreement_at_left {lo hi x y tau : ℝ}
    (hclose : |x - y| ≤ tau)
    (hdiff : ¬(x ∈ Set.Ico lo hi ↔ y ∈ Set.Ico lo hi)) :
    |x - lo| ≤ tau ∨ |x - hi| ≤ tau := by
  obtain ⟨hlo, hhi⟩ := abs_le.mp hclose
  by_cases hx : x ∈ Set.Ico lo hi
  · have hy : y ∉ Set.Ico lo hi := fun hy => hdiff (iff_of_true hx hy)
    have hy' : y < lo ∨ hi ≤ y := by
      simpa only [Set.mem_Ico, not_and_or, not_le, not_lt] using hy
    rcases hy' with hy' | hy'
    · exact Or.inl (abs_le.mpr ⟨by linarith [hx.1], by linarith [hx.1]⟩)
    · exact Or.inr (abs_le.mpr ⟨by linarith [hx.2], by linarith [hx.2]⟩)
  · have hy : y ∈ Set.Ico lo hi := by
      by_contra hy
      exact hdiff (iff_of_false hx hy)
    by_cases hxlo : x < lo
    · exact Or.inl (abs_le.mpr ⟨by linarith [hy.1], by linarith [hy.1]⟩)
    · have hxhi : hi ≤ x := by
        by_contra h
        exact hx ⟨le_of_not_gt hxlo, lt_of_not_ge h⟩
      exact Or.inr (abs_le.mpr ⟨by linarith [hy.2], by linarith [hy.2]⟩)

theorem exponentCode_disagreement_boundary {a b : ℝ} (hab : a < b)
    {mesh : ℕ} {x y tau : ℝ} (hclose : |x - y| ≤ tau)
    (hdiff : exponentCode a b mesh x ≠ exponentCode a b mesh y) :
    ∃ j : Fin (mesh + 2), |x - logPrimeMeshPoint a b mesh j.val| ≤ tau := by
  have hinterval : ∃ j : Fin (mesh + 1),
      ¬(x ∈ Set.Ico (logPrimeMeshPoint a b mesh j.val)
          (logPrimeMeshPoint a b mesh (j.val + 1)) ↔
        y ∈ Set.Ico (logPrimeMeshPoint a b mesh j.val)
          (logPrimeMeshPoint a b mesh (j.val + 1))) := by
    cases hx : exponentCode a b mesh x with
    | none =>
        cases hy : exponentCode a b mesh y with
        | none => exact (hdiff (hx.trans hy.symm)).elim
        | some j =>
            refine ⟨j, ?_⟩
            intro h
            have hxin := h.mpr (exponentCode_some_membership hy)
            have hxc := exponentCode_eq_of_mesh_interval hab j hxin
            exact hdiff (hxc.trans hy.symm)
    | some j =>
        refine ⟨j, ?_⟩
        intro h
        have hyin := h.mp (exponentCode_some_membership hx)
        exact hdiff (hx.trans (exponentCode_eq_of_mesh_interval hab j hyin).symm)
  obtain ⟨j, hj⟩ := hinterval
  rcases interval_disagreement_at_left hclose hj with hlo | hhi
  · exact ⟨⟨j.val, by omega⟩, hlo⟩
  · exact ⟨⟨j.val + 1, by omega⟩, hhi⟩

theorem coarseWord_disagreement_coordinate {a b : ℝ} {mesh : ℕ}
    {xs ys : List ℝ} (hlen : xs.length = ys.length)
    (h : coarseWord a b mesh xs ≠ coarseWord a b mesh ys) :
    ∃ i : Fin xs.length,
      exponentCode a b mesh xs[i.val] ≠
        exponentCode a b mesh (getElem ys i.val (by omega)) := by
  by_contra hn
  push_neg at hn
  apply h
  apply List.ext_getElem
  · simpa only [coarseWord, List.length_map] using hlen
  · intro i hi hi'
    have hix : i < xs.length := by simpa only [coarseWord, List.length_map] using hi
    simpa only [coarseWord, List.getElem_map] using hn ⟨i, hix⟩

end
end ImbalancedChen.P3OriginalU5WarmWordWalls
