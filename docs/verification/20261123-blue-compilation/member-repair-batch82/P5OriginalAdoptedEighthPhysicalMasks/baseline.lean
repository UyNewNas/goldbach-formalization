import ImbalancedChen.P4AOriginalEighthParentPhysicalLedger
import ImbalancedChen.SelectedPrefixBoxCap
import ImbalancedChen.ActualSmallRoughAttachment
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

This source records the manuscript's actual 87 adopted eighth-domain slots:
30 equal-parent mask129; 13 unequal winner9 mask138; one each unequal
winner50 A/D with masks184/134; 13 ascending-pair mask138; and 12+7+10
first-failure mask138. The finite affine-cell certificates and the common
causal third/sixth parent realization are separate guarded dependencies.
No numerical gain or new distribution theorem is asserted here.

All squares use the *physical* eighth exponent. The finite auxiliary
covering cutoff occurs only in the prime carrier, never as that exponent.
-/

namespace ImbalancedChen.P5OriginalAdoptedEighthPhysicalMasks

noncomputable section
open scoped Classical BigOperators
open VariableEnvelope

abbrev Point := Fin 8 → ℝ
abbrev Cell := Fin 87

def mask129 : Finset (Fin 8) := {0, 7}
def mask138 : Finset (Fin 8) := {1, 3, 7}
def mask184 : Finset (Fin 8) := {3, 4, 5, 7}
def mask134 : Finset (Fin 8) := {1, 2, 7}

/-- The finite indexing is the published 30+13+1+1+13+12+7+10 partition.
The 50A and 50D cells occupy indices 43 and 44. -/
def selectedMask (i : Cell) : Finset (Fin 8) :=
  if i.val < 30 then mask129
  else if i.val = 43 then mask184
  else if i.val = 44 then mask134
  else mask138

def S (t : Point) : ℝ := ∑ j, t j
def H1 (t : Point) : ℝ := 3 * t 0
def H3 (t : Point) : ℝ := t 0 + t 1 + 3 * t 2
def H5 (t : Point) : ℝ := t 0 + t 1 + t 2 + t 3 + 3 * t 4
def H7 (t : Point) : ℝ := (∑ j ∈ Finset.univ.filter (fun j : Fin 8 => j < 6), t j) + 3 * t 6
def d (t : Point) : ℝ := t 1 + t 2
def e (t : Point) : ℝ := t 0 + t 3
def eta : ℝ := 1 / 1000000

/-- Literal old comparison R6 on the eight published components. -/
def oldComparison (i : Cell) (t : Point) : ℝ :=
  if i.val < 30 then C (d t)
  else if i.val = 43 then A (t 1 + t 4 + t 5)
  else if i.val = 44 then C (t 1 + t 4 + t 5)
  else A (e t)

/-- The third minorant is a sufficient retained-history bound, not an
identity for the actual third cap. -/
def thirdMinorant (i : Cell) (t : Point) : ℝ :=
  if i.val < 43 then C (d t)
  else if i.val = 43 then A (d t)
  else if i.val = 44 then A (t 0)
  else if i.val < 58 then A (d t)
  else A (t 0)

/-- The four literal new tent expressions, including their fixed buffer. -/
def newCap (i : Cell) (t : Point) : ℝ :=
  if i.val < 30 then v (t 0 + t 7) - eta
  else if i.val = 43 then A (t 3 + t 4 + t 5 + t 7) - eta
  else if i.val = 44 then C (t 1 + t 2 + t 7) - eta
  else A (t 1 + t 3 + t 7) - eta

/-- The old third-minorant split and the first failed old D23 history.
Failure here is of a sufficient comparison test, not a first exit of the
true retained tree. -/
def publishedGroupSide (i : Cell) (t : Point) : Prop :=
  if i.val < 30 then True
  else if i.val < 43 then mu < d t
  else if i.val = 43 then d t < mu
  else if i.val = 44 then t 0 < mu
  else if i.val < 58 then d t < mu
  else if i.val < 70 then
    mu < d t ∧ H1 t < C (d t) ∧ C (d t) < H3 t
  else if i.val < 77 then
    mu < d t ∧ H1 t < C (d t) ∧ H3 t < C (d t) ∧ C (d t) < H5 t
  else
    mu < d t ∧ H1 t < C (d t) ∧ H3 t < C (d t) ∧
      H5 t < C (d t) ∧ C (d t) < H7 t

theorem all_cells_partition (i : Cell) :
    i.val < 30 ∨ (30 ≤ i.val ∧ i.val < 43) ∨ i.val = 43 ∨ i.val = 44 ∨
      (45 ≤ i.val ∧ i.val < 58) ∨ (58 ≤ i.val ∧ i.val < 70) ∨
      (70 ≤ i.val ∧ i.val < 77) ∨ (77 ≤ i.val ∧ i.val < 87) := by
  have hi := i.isLt
  omega

/-- The row fields are the retained physical tests in the manuscript's
finite strict-cell certificates. Their instantiation for each of the 87
published affine cells is deliberately exposed as a dependency. -/
structure PhysicalRows (i : Cell) (t : Point) (lambda3 current : ℝ) : Prop where
  group_side : publishedGroupSide i t
  last_positive : 53 / 13824 < t 7
  ordered_last : t 7 < t 6
  first_cube : H1 t < lambda3
  third_cube : H3 t < lambda3
  fifth_cube : H5 t < lambda3
  third_history : H7 t < lambda3
  selected_license : newCap i t < v (∑ j ∈ selectedMask i, t j)
  third_to_sixth : lambda3 ≤ current
  sixth_upper : current ≤ oldComparison i t
  improvement : oldComparison i t < newCap i t
  terminal : newCap i t < S t + 3 * t 7
  full_squares : ∀ j, prefixSquareExpr t j < newCap i t
  complement_squares : ∀ j ∉ selectedMask i,
    selectedSquareExpr (selectedMask i) t j < newCap i t

/-- The physical current parent is in the ordinary initial residual
range. The comparison R6 bounds it from above; it does not replace it. -/
theorem PhysicalRows.current_residual_gt_last {i : Cell} {t : Point}
    {lambda3 current : ℝ} (h : PhysicalRows i t lambda3 current) :
    t 7 < current - S t := by
  have hS : S t = t 0 + t 1 + t 2 + t 3 + t 4 + t 5 + t 6 + t 7 := by
    simp [S, Fin.sum_univ_succ] <;> ring
  have hH : H7 t = t 0 + t 1 + t 2 + t 3 + t 4 + t 5 + 3 * t 6 := by
    simp [H7, Fin.sum_univ_succ] <;> ring
  rw [hS] at *
  rw [hH] at *
  linarith [h.third_history, h.third_to_sixth, h.ordered_last]

theorem PhysicalRows.new_residual_lt_three_last {i : Cell} {t : Point}
    {lambda3 current : ℝ} (h : PhysicalRows i t lambda3 current) :
    newCap i t - S t < 3 * t 7 := by
  linarith [h.terminal]

/-- The raised exponent is below the original physical Theta; the
auxiliary factorization cover does not enter this comparison. -/
theorem PhysicalRows.newCap_lt_physicalTheta {i : Cell} {t : Point}
    {lambda3 current : ℝ} (h : PhysicalRows i t lambda3 current) :
    newCap i t < (299 / 500 : ℝ) := by
  have hcap : VariableEnvelope.cap < (299 / 500 : ℝ) := by
    norm_num [VariableEnvelope.cap]
  exact (h.selected_license.trans_le (v_le_cap _)).trans hcap

/-- Every full and selected-complement square is at the same new physical
level. This is the exact hypothesis used by the selected-product compiler. -/
theorem PhysicalRows.actual_integer_square_gates {i : Cell} {t : Point}
    {lambda3 current : ℝ} (h : PhysicalRows i t lambda3 current)
    (N : ℝ) (hN : 1 < N) (p : Fin 8 → ℕ)
    (hp : ∀ j, (p j : ℝ) ≤ N ^ t j) :
    (∀ j, ((∏ k ∈ Finset.univ.filter (fun k : Fin 8 => k < j), p k : ℕ) : ℝ) *
      (p j : ℝ) ^ 2 < N ^ newCap i t) ∧
    (∀ j ∉ selectedMask i,
      ((∏ k ∈ selectedMask i, p k : ℕ) : ℝ) *
        ((∏ k ∈ Finset.univ.filter (fun k : Fin 8 => k < j ∧ k ∉ selectedMask i),
          p k : ℕ) : ℝ) * (p j : ℝ) ^ 2 < N ^ newCap i t) := by
  exact ⟨fun j => prefixSquareExpr_actual_gate N hN p t hp j (h.full_squares j),
    fun j hj => selectedSquareExpr_actual_gate (selectedMask i) N hN p t hp j
      (h.complement_squares j hj)⟩

/-- Once a selected mask has occurred, a later selected-complement square
is literally the full square. The retained residual therefore needs only
the ordinary full-square gate at later ranks. -/
theorem complement_square_eq_full_after_mask {n : ℕ} (I : Finset (Fin n))
    (t : Fin n → ℝ) (j : Fin n) (hbefore : ∀ i ∈ I, i < j) :
    selectedSquareExpr I t j = prefixSquareExpr t j := by
  let C : Finset (Fin n) := Finset.univ.filter (fun k => k < j ∧ k ∉ I)
  let P : Finset (Fin n) := Finset.univ.filter (fun k => k < j)
  have hd : Disjoint I C := by
    apply Finset.disjoint_left.mpr
    intro i hi hC
    exact (Finset.mem_filter.mp hC).2.2 hi
  have hu : I ∪ C = P := by
    ext i
    by_cases hi : i ∈ I
    · simp [C, P, hi, hbefore i hi]
    · simp [C, P, hi]
  unfold selectedSquareExpr prefixSquareExpr
  change (∑ i ∈ I, t i) + (∑ i ∈ C, t i) + 2 * t j =
    (∑ i ∈ P, t i) + 2 * t j
  rw [← Finset.sum_union hd, hu]

/-- The actual sixth policy stays the parent. A domain is consulted only
at rank eight, with lambda3 and lambda6 frozen at their own ancestors. -/
def parentPolicy (N : ℝ) (lambda6 : List ℕ → ℝ)
    (base : Bool → List ℕ → Bool) : Bool → List ℕ → Bool :=
  P4AOriginalEighthParentPhysicalLedger.parentPolicy N lambda6 base

def adoptedGuard (N : ℝ) (lambda3 lambda6 : List ℕ → ℝ)
    (pre : List ℕ) : Prop :=
  ∃ i : Cell, PhysicalRows i (primeHistoryLogCoordinates N 8 pre)
    (lambda3 (rosserAncestor 3 pre)) (lambda6 (rosserAncestor 6 pre))

def raisedExponent (N : ℝ) (lambda3 lambda6 : List ℕ → ℝ)
    (pre : List ℕ) : ℝ :=
  if h : adoptedGuard N lambda3 lambda6 pre then
    newCap (Classical.choose h) (primeHistoryLogCoordinates N 8 pre)
  else lambda6 (rosserAncestor 6 pre)

theorem actual_sixth_le_raised (N : ℝ) (lambda3 lambda6 : List ℕ → ℝ)
    (pre : List ℕ) :
    lambda6 (rosserAncestor 6 pre) ≤ raisedExponent N lambda3 lambda6 pre := by
  unfold raisedExponent
  split_ifs with h
  · have hr := Classical.choose_spec h
    exact hr.sixth_upper.trans hr.improvement.le
  · exact le_rfl

def familyPolicy (N : ℝ) (lambda3 lambda6 : List ℕ → ℝ)
    (base : Bool → List ℕ → Bool) : Bool → List ℕ → Bool :=
  firstExitDepthSplicePolicy 8 (parentPolicy N lambda6 base)
    (frozenParityRosserPolicy false 8 (fun pre => N ^ raisedExponent N lambda3 lambda6 pre))

theorem family_even (N : ℝ) (lambda3 lambda6 : List ℕ → ℝ)
    (base : Bool → List ℕ → Bool) (hbase : ∀ pre, base true pre = true)
    (pre : List ℕ) : familyPolicy N lambda3 lambda6 base true pre = true := by
  exact UpperPolicyFiniteBridge.firstExitDepthSplicePolicy_even_retained 8 _ _
    (P4AOriginalEighthParentPhysicalLedger.parent_even N lambda6 base hbase)
    (fun q => frozenParityRosserPolicy_upper_even 8 _ q) pre

/-- The eighth family changes only the rough first-exit policy. The same
small beta pair is attached after the rough sign is known. -/
theorem adopted_leaf_physical_coefficient
    (N cap : ℕ) (w z L : ℝ) (lambda3 lambda6 : List ℕ → ℝ)
    (base : Bool → List ℕ → Bool) (hbase : ∀ pre, base true pre = true)
    (leaf : FirstExitLeaf ℕ)
    (hleaf : leaf ∈ firstExitRootLeaves
      (familyPolicy (N : ℝ) lambda3 lambda6 base) (fun _ => 1)
      (roughPrimeUniverse N cap w z))
    (a : ℕ) (ha : a ∈ actualSmallRosserSupport N cap w) :
    let R := familyPolicy (N : ℝ) lambda3 lambda6 base
    let q := a * leaf.selected.prod
    q ∈ actualSmallRoughModuli (R false) N cap w z ∧
      Squarefree q ∧ q.Coprime N ∧
      |actualSmallRoughRho (R false) N cap w z L q| ≤ 1 ∧
      actualSmallRoughRho (R false) N cap w z L q =
        signAttachedCoefficient
          (firstExitRetainedCoefficient R (roughPrimeUniverse N cap w z)
            leaf.selected.prod : ℝ)
          (actualSmallRosserMinus N cap w L a)
          (actualSmallRosserPlus N cap w L a) := by
  dsimp only
  let R := familyPolicy (N : ℝ) lambda3 lambda6 base
  let d := leaf.selected.prod
  have hd : d ∈ firstExitRetainedModuli R (roughPrimeUniverse N cap w z) :=
    (mem_firstExitRetainedModuli R _ d).mpr ⟨leaf, hleaf, rfl⟩
  have hdFixed : d ∈ fixedRoughSupport (R false) N cap w z := by
    rw [UpperPolicyFiniteBridge.fixedRoughSupport_eq_firstExitRetainedModuli_of_even_retained
      R (family_even (N : ℝ) lambda3 lambda6 base hbase) N cap w z]
    exact hd
  have hq : a * d ∈ actualSmallRoughModuli (R false) N cap w z :=
    Finset.mem_image.mpr ⟨(a, d), Finset.mem_product.mpr ⟨ha, hdFixed⟩, rfl⟩
  refine ⟨hq, actualSmallRoughModuli_squarefree (R false) N cap w z hq,
    actualSmallRoughModuli_coprime_target (R false) N cap w z hq,
    actualSmallRoughRho_abs_le_one (R false) N cap w z L (a * d), ?_⟩
  change smallRoughRho (actualSmallRosserSupport N cap w)
    (fixedRoughSupport (R false) N cap w z)
    (fixedRoughCoefficient (R false) N cap w z)
    (actualSmallRosserMinus N cap w L) (actualSmallRosserPlus N cap w L) (a * d) = _
  rw [smallRoughRho_mul
    (fun _ hx => actualSmallRosserSupport_smallPrimeSupportedAt N cap w hx)
    (fun _ hx => fixedRoughSupport_roughPrimeSupportedAt (R false) N cap w z hx)
    (fixedRoughCoefficient (R false) N cap w z)
    (actualSmallRosserMinus N cap w L) (actualSmallRosserPlus N cap w L) ha hdFixed]
  change signAttachedCoefficient (fixedRoughCoefficient (R false) N cap w z d)
    (actualSmallRosserMinus N cap w L a) (actualSmallRosserPlus N cap w L a) = _
  rw [UpperPolicyFiniteBridge.fixedRoughCoefficient_eq_firstExitRetainedCoefficient_of_even_retained
    R (family_even (N : ℝ) lambda3 lambda6 base hbase) N cap w z d]

/-- The scalar and arithmetic support consequences apply to every
nonzero coefficient of this very same 87-domain policy, including earlier
inherited leaves. No abstract family-indexed coefficient is substituted. -/
theorem adopted_nonzero_physical_support
    (N cap : ℕ) (w z L : ℝ) (lambda3 lambda6 : List ℕ → ℝ)
    (base : Bool → List ℕ → Bool) (q : ℕ)
    (hq : actualSmallRoughRho
      ((familyPolicy (N : ℝ) lambda3 lambda6 base) false) N cap w z L q ≠ 0) :
    q ∈ actualSmallRoughModuli
        ((familyPolicy (N : ℝ) lambda3 lambda6 base) false) N cap w z ∧
      Squarefree q ∧ q.Coprime N ∧
      |actualSmallRoughRho
        ((familyPolicy (N : ℝ) lambda3 lambda6 base) false) N cap w z L q| ≤ 1 := by
  let R := (familyPolicy (N : ℝ) lambda3 lambda6 base) false
  obtain ⟨a, ha, b, hb, hprod, _haL, _hrough⟩ :=
    actualSmallRoughRho_ne_zero_factors R N cap w z L hq
  have hmem : q ∈ actualSmallRoughModuli R N cap w z := by
    rw [hprod]
    exact Finset.mem_image.mpr ⟨(a, b), Finset.mem_product.mpr ⟨ha, hb⟩, rfl⟩
  exact ⟨hmem, actualSmallRoughModuli_squarefree R N cap w z hmem,
    actualSmallRoughModuli_coprime_target R N cap w z hmem,
    actualSmallRoughRho_abs_le_one R N cap w z L q⟩

end
end ImbalancedChen.P5OriginalAdoptedEighthPhysicalMasks
