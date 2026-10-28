import ImbalancedChen.P5OriginalH3Cell00StrictOldPlanes
import ImbalancedChen.P5OriginalPhaseBPhysicalBinding
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The first-failure H3 cell00 is thickened to a concrete open rational box.
Every physical row holds throughout this box, not only at its center.
The third and sixth exponents remain those of the SAME causal ancestors.
Their four scalar comparisons are stated explicitly; no global ancestor
supplier, density, PP estimate or final upper bound is assumed or proved.

The guard in the predecessor is existential over all 87 slots. A witness
at slot 58 does not by itself identify its Classical.choose value. Here
all other possible choices are shown to use the SAME mask138 and new cap:
slots <30 and 43,44 are excluded by the actual sixth lower comparison.
Thus the physical raised exponent and selected mask are unambiguous on
this local box even before a global disjoint-owner implementation exists.
-/

namespace ImbalancedChen.P5OriginalH3Cell00PhysicalBoxBinding

noncomputable section
open scoped Classical BigOperators
open VariableEnvelope
open P5OriginalAdoptedEighthPhysicalMasks
open P5OriginalEighthAffineRowRecipe
open P5OriginalEighthNavigationMap
open P5OriginalEighthPhysicalRowBag
open P5OriginalH3Cell00StrictOldPlanes

/-- Fixed rational side radius, chosen before any arithmetic parameter N. -/
def boxRadius : ℝ := 1 / 100000000

/-- An open eight-dimensional box around the published exact center. -/
def InBox (t : Point) : Prop :=
  ∀ j, strictCenter j - boxRadius < t j ∧
    t j < strictCenter j + boxRadius

private theorem box_coordinates {t : Point} (h : InBox t) :
    (strictCenter 0 - boxRadius < t 0 ∧ t 0 < strictCenter 0 + boxRadius) ∧
    (strictCenter 1 - boxRadius < t 1 ∧ t 1 < strictCenter 1 + boxRadius) ∧
    (strictCenter 2 - boxRadius < t 2 ∧ t 2 < strictCenter 2 + boxRadius) ∧
    (strictCenter 3 - boxRadius < t 3 ∧ t 3 < strictCenter 3 + boxRadius) ∧
    (strictCenter 4 - boxRadius < t 4 ∧ t 4 < strictCenter 4 + boxRadius) ∧
    (strictCenter 5 - boxRadius < t 5 ∧ t 5 < strictCenter 5 + boxRadius) ∧
    (strictCenter 6 - boxRadius < t 6 ∧ t 6 < strictCenter 6 + boxRadius) ∧
    (strictCenter 7 - boxRadius < t 7 ∧ t 7 < strictCenter 7 + boxRadius) :=
  ⟨h 0, h 1, h 2, h 3, h 4, h 5, h 6, h 7⟩

/-- The open box is nonempty; it is not a singleton-center assertion. -/
theorem center_mem_box : InBox strictCenter := by
  intro j
  constructor <;> dsimp [boxRadius] <;> linarith

/-- The box lies inside the source's strict ordered/activated region. -/
theorem box_source_geometry {t : Point} (ht : InBox t) :
    StrictAnti t ∧ 0 < t 7 ∧ t 0 < mu ∧ 1 / 100 < t 2 := by
  rcases box_coordinates ht with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;>
      norm_num [strictCenter, boxRadius] at * <;> linarith
  · norm_num [strictCenter, boxRadius] at * <;> linarith
  · norm_num [mu, strictCenter, boxRadius] at * <;> linarith
  · norm_num [strictCenter, boxRadius] at * <;> linarith

/-- Each of the 62 proper old planes remains strictly below R6 on the
whole box. The mask9 equality is kept as an identity, never buffered. -/
theorem box_proper_old_planes {t : Point} (ht : InBox t) :
    ∀ I ∈ oldMasks, I ≠ winnerMask →
      (if oldMaskCode I ∈ firstFailureH3LeftCodes 0 then
          A (oldSubsetSum t I)
        else C (oldSubsetSum t I)) < oldComparison slot t := by
  rcases box_coordinates ht with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  intro I hI hne
  fin_cases I <;>
    norm_num [oldMasks, winnerMask, slot, oldMaskCode,
      firstFailureH3LeftCodes, oldSubsetSum, oldComparison,
      strictCenter, boxRadius, e, A, C] at * <;> linarith

/-- All 63 assigned old rows hold, including the unavoidable equality. -/
theorem box_old_planes {t : Point} (ht : InBox t) :
    oldPlaneRows slot (firstFailureH3LeftCodes 0) t := by
  intro I hI
  by_cases h : I = winnerMask
  · subst I
    exact le_of_eq (winner_plane_identity t)
  · exact (box_proper_old_planes ht I hI h).le

/-- All local physical obligations are now proved from rational box
membership and the actual ancestor's four scalar comparisons. -/
theorem box_physical_rows {t : Point} (ht : InBox t)
    {lambda3 current : ℝ}
    (hthird : (567 / 1000 : ℝ) ≤ lambda3)
    (hmono : lambda3 ≤ current)
    (hupper : current ≤ oldComparison slot t) :
    PhysicalRows slot t lambda3 current := by
  rcases box_coordinates ht with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hmono, hupper, ?_, ?_, ?_, ?_⟩
  · norm_num [publishedGroupSide, slot, d, H1, H3, mu, C,
      strictCenter, boxRadius] at *
    constructor <;> try constructor <;> linarith
  · norm_num [strictCenter, boxRadius] at * <;> linarith
  · norm_num [strictCenter, boxRadius] at * <;> linarith
  · norm_num [H1, strictCenter, boxRadius] at * <;> linarith
  · norm_num [H3, strictCenter, boxRadius] at * <;> linarith
  · norm_num [H5, strictCenter, boxRadius] at * <;> linarith
  · norm_num [H7, Finset.sum_filter, Fin.sum_univ_succ,
      strictCenter, boxRadius] at * <;> linarith
  · rw [v_eq_min]
    apply lt_min
    · norm_num [newCap, slot, selectedMask, mask138, eta, A] <;> linarith
    · norm_num [newCap, slot, selectedMask, mask138, eta, A, C,
        strictCenter, boxRadius] at *
      linarith
  · norm_num [oldComparison, newCap, slot, e, eta, A,
      strictCenter, boxRadius] at * <;> linarith
  · norm_num [newCap, slot, S, eta, A, Fin.sum_univ_succ,
      strictCenter, boxRadius] at * <;> linarith
  · intro j
    fin_cases j <;>
      norm_num [newCap, slot, eta, A, prefixSquareExpr,
        Finset.sum_filter, Fin.sum_univ_succ, strictCenter, boxRadius] at * <;>
      linarith
  · intro j hj
    fin_cases j <;>
      norm_num [selectedMask, slot, mask138, newCap, eta, A,
        selectedSquareExpr, Finset.sum_filter, Fin.sum_univ_succ,
        strictCenter, boxRadius] at * <;> linarith

/-- One pair of rational caps works on the WHOLE local box. The third
cap is strictly below the original baseline minorant v(t1). This is a
local common-cap construction, not a supplied all-domain ancestor table. -/
theorem local_constant_caps {t : Point} (ht : InBox t) :
    PhysicalRows slot t (567 / 1000) (596 / 1000) ∧
      (567 / 1000 : ℝ) < v (t 0) := by
  rcases box_coordinates ht with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  have hu : (596 / 1000 : ℝ) ≤ oldComparison slot t := by
    norm_num [oldComparison, slot, e, A, strictCenter, boxRadius] at * <;> linarith
  refine ⟨box_physical_rows ht le_rfl (by norm_num) hu, ?_⟩
  rw [v_eq_A (box_source_geometry ht).2.2.1.le]
  norm_num [A, strictCenter, boxRadius] at *
  linarith

/-- The scalar lower bound of the sixth ancestor excludes all slots
whose cap formula differs from this H3 cell's formula. -/
theorem every_guard_same_mask_and_cap {t : Point} (ht : InBox t)
    {lambda3 current : ℝ} (hcurrent : (596 / 1000 : ℝ) ≤ current)
    (i : Cell) (hi : PhysicalRows i t lambda3 current) :
    selectedMask i = mask138 ∧ newCap i t = newCap slot t := by
  rcases box_coordinates ht with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  have hnot30 : ¬i.val < 30 := by
    intro hlt
    have hu := hi.sixth_upper
    norm_num [oldComparison, hlt, d, C, strictCenter, boxRadius] at * <;> linarith
  have hnot43 : i.val ≠ 43 := by
    intro heq
    have hu := hi.sixth_upper.trans_lt hi.improvement
    norm_num [newCap, hnot30, heq, eta, A, strictCenter, boxRadius] at * <;> linarith
  have hnot44 : i.val ≠ 44 := by
    intro heq
    have hu := hi.sixth_upper.trans_lt hi.improvement
    norm_num [newCap, hnot30, hnot43, heq, eta, C,
      strictCenter, boxRadius] at * <;> linarith
  constructor
  · simp [selectedMask, hnot30, hnot43, hnot44]
  · simp [newCap, hnot30, hnot43, hnot44, slot]

/-- Concrete source rows joined to actual arithmetic log coordinates.
Both cap values are evaluated on the same pre's causal ancestors. -/
theorem actual_h3_guard_and_choice
    (N : ℝ) (lambda3 lambda6 : List ℕ → ℝ) (pre : List ℕ)
    (hbox : InBox (primeHistoryLogCoordinates N 8 pre))
    (hthird : (567 / 1000 : ℝ) ≤ lambda3 (rosserAncestor 3 pre))
    (hcurrent : (596 / 1000 : ℝ) ≤ lambda6 (rosserAncestor 6 pre))
    (hmono : lambda3 (rosserAncestor 3 pre) ≤ lambda6 (rosserAncestor 6 pre))
    (hupper : lambda6 (rosserAncestor 6 pre) ≤
      oldComparison slot (primeHistoryLogCoordinates N 8 pre)) :
    ∃ h : adoptedGuard N lambda3 lambda6 pre,
      selectedMask (Classical.choose h) = mask138 ∧
      raisedExponent N lambda3 lambda6 pre =
        newCap slot (primeHistoryLogCoordinates N 8 pre) ∧
      ∀ row ∈ physicalRowBag slot,
        rowHolds slot (firstFailureH3LeftCodes 0)
          (primeHistoryLogCoordinates N 8 pre) row := by
  have hp := box_physical_rows hbox hthird hmono hupper
  have hg : adoptedGuard N lambda3 lambda6 pre := ⟨slot, hp⟩
  have hc := every_guard_same_mask_and_cap hbox hcurrent
    (Classical.choose hg) (Classical.choose_spec hg)
  refine ⟨hg, hc.1, ?_, ?_⟩
  · simp only [raisedExponent, dif_pos hg]
    exact hc.2
  · exact (physical_row_bag_holds_iff slot (firstFailureH3LeftCodes 0) _).2
      ⟨box_old_planes hbox, hp.full_squares, hp.complement_squares⟩

/-- The selected-product compiler sees all eight full squares and all
five complementary squares at the same raised physical exponent. -/
theorem actual_h3_integer_square_gates
    (N : ℝ) (hN : 1 < N) (lambda3 lambda6 : List ℕ → ℝ)
    (pre : List ℕ) (p : Fin 8 → ℕ)
    (hp : ∀ j, (p j : ℝ) ≤ N ^ primeHistoryLogCoordinates N 8 pre j)
    (hbox : InBox (primeHistoryLogCoordinates N 8 pre))
    (hthird : (567 / 1000 : ℝ) ≤ lambda3 (rosserAncestor 3 pre))
    (hcurrent : (596 / 1000 : ℝ) ≤ lambda6 (rosserAncestor 6 pre))
    (hmono : lambda3 (rosserAncestor 3 pre) ≤ lambda6 (rosserAncestor 6 pre))
    (hupper : lambda6 (rosserAncestor 6 pre) ≤
      oldComparison slot (primeHistoryLogCoordinates N 8 pre)) :
    (∀ j, ((∏ k ∈ Finset.univ.filter (fun k : Fin 8 => k < j), p k : ℕ) : ℝ) *
      (p j : ℝ) ^ 2 < N ^ raisedExponent N lambda3 lambda6 pre) ∧
    (∀ j ∉ mask138,
      ((∏ k ∈ mask138, p k : ℕ) : ℝ) *
        ((∏ k ∈ Finset.univ.filter (fun k : Fin 8 => k < j ∧ k ∉ mask138),
          p k : ℕ) : ℝ) * (p j : ℝ) ^ 2 <
        N ^ raisedExponent N lambda3 lambda6 pre) := by
  obtain ⟨hg, _, hcap, _⟩ :=
    actual_h3_guard_and_choice N lambda3 lambda6 pre hbox hthird hcurrent hmono hupper
  rw [hcap]
  have hrows := box_physical_rows hbox hthird hmono hupper
  simpa [selectedMask, slot] using hrows.actual_integer_square_gates N hN p hp

/-- The local physical tests and their unambiguous cap are bound to the
same signed small/rough coefficient of the corrected-parent policy.
This proves no positivity or density estimate for a differently chosen rho. -/
theorem actual_h3_same_rho_support
    (e chi : ℝ) (m : ℕ) (omega : ℝ)
    (N cap : ℕ) (w z L : ℝ) (lambda3 lambda6 : List ℕ → ℝ)
    (pre : List ℕ)
    (hbox : InBox (primeHistoryLogCoordinates (N : ℝ) 8 pre))
    (hthird : (567 / 1000 : ℝ) ≤ lambda3 (rosserAncestor 3 pre))
    (hcurrent : (596 / 1000 : ℝ) ≤ lambda6 (rosserAncestor 6 pre))
    (hmono : lambda3 (rosserAncestor 3 pre) ≤ lambda6 (rosserAncestor 6 pre))
    (hupper : lambda6 (rosserAncestor 6 pre) ≤
      oldComparison slot (primeHistoryLogCoordinates (N : ℝ) 8 pre))
    (q : ℕ) (hq :
      P5OriginalPhaseBPhysicalBinding.physicalRho e chi m omega N cap
        w z L lambda3 lambda6 q ≠ 0) :
    raisedExponent (N : ℝ) lambda3 lambda6 pre =
      newCap slot (primeHistoryLogCoordinates (N : ℝ) 8 pre) ∧
    q ∈ actualSmallRoughModuli
      ((P5OriginalPhaseBPhysicalBinding.physicalPolicy e chi m omega
        (N : ℝ) lambda3 lambda6) false) N cap w z ∧
    Squarefree q ∧ q.Coprime N ∧
    |P5OriginalPhaseBPhysicalBinding.physicalRho e chi m omega N cap
      w z L lambda3 lambda6 q| ≤ 1 := by
  obtain ⟨hg, _, hcap, _⟩ := actual_h3_guard_and_choice
    (N : ℝ) lambda3 lambda6 pre hbox hthird hcurrent hmono hupper
  exact ⟨hcap, P5OriginalPhaseBPhysicalBinding.physical_rho_nonzero_support
    e chi m omega N cap w z L lambda3 lambda6 q hq⟩

end
end ImbalancedChen.P5OriginalH3Cell00PhysicalBoxBinding
