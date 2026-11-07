import ImbalancedChen.P5OriginalCommonRefinedConstructor

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Actual missing catalog entry8, NOT entry7's ascending tent33 cells.
The independent frozen author/independent sources both select patterns
1371 and1867 with M=D(t0+t5)-10^-6, old comparison R0=(1+t0)/2,
clippedCap>A33 and D33<A33-eta. The physical decode and branch program
are the original six-coordinate ones. REGISTRY pins their raw bytes.
No simplex enclosure, numerical gain or new policy is assumed.

A one-sided tent increment estimate and the source's actual old31 planes
show that these strict source rows are incompatible with EVERY entry7
PhysicalCell. Consequently the existing actual all11 constructor has
lambda6=actualParent5 on this source. The original positive entry8 profile
is kept separate from its zero current-sixth-change profile. This is an
exact missing source binding in the incomplete constructor, not a theorem
that the manuscript is false or that the total earlier gain is lost.
Full22/full87 identity, geometry/owner/Family and archived-total accounting
remain open. No constructed expanded policy is labelled the original one.
-/
namespace ImbalancedChen.P5Z.OriginalDescending33ActualOmission
noncomputable section
open Classical
open scoped BigOperators
open Certificates.P2OriginalSixthElevenLogSemantics
open P5OriginalCommonRefinedConstructor

inductive Pattern where
  | p1371 | p1867
  deriving DecidableEq, Repr

/-- Shared ONLY for the literal original old31 branch bits. This does
not identify the descending source with the all11 ascending source cell. -/
def oldBranchCell : Pattern → Cell
  | .p1371 => .tent33_1371
  | .p1867 => .tent33_1867

def descendingNewCap (t : Physical) : ℝ := descending33 t-eta

/-- Literal frozen `physical(q)` with q=(x,y,z,a,c,r), defined separately
before proving its agreement with the original source chart. -/
def sourcePhysical (q : Physical) : Physical :=
  ![q 0,q 1,q 2,(1-q 0)/2-q 1-q 2+(q 4-3*q 3)/2,(q 3-q 4)/2,q 5]

theorem sourcePhysical_eq_original_decode (q : Physical) : sourcePhysical q = physical q := by
  ext i
  fin_cases i <;> simp [sourcePhysical,physical] <;> ring

/-- Literal frozen values(q) factor order, with two residual factors and
six physical coordinates, not a reassigned eighth-domain measure. -/
def sourceFactors (t : Physical) : Fin 8 → ℝ :=
  ![R0 t-S6 t,descendingNewCap t-S6 t,t 0,t 1,t 2,t 3,t 4,t 5]

theorem sourceFactors_product (t : Physical) :
    (∏ i,sourceFactors t i) =
      (R0 t-S6 t)*(descendingNewCap t-S6 t)*coordinateProduct t := by
  simp [sourceFactors,coordinateProduct,Fin.prod_univ_succ] <;> ring

/-- The actual strict physical rows of the frozen descending33 source.
Old subset/winner planes remain closed. The old/new residual and squares
share the very same source t, selected mask33={0,5}, and cutoff t5. -/
structure PhysicalSource (p : Pattern) (t : Physical) : Prop where
  rpos : 0 < t 5
  order : t 5 < t 4 ∧ t 4 < t 3 ∧ t 3 < t 2 ∧ t 2 < t 1 ∧ t 1 < t 0
  largest : t 0 < mu
  oldCutoff : t 5 < 1/50
  compactCutoff : 53/4608 < t 5
  history3 : H3 t < R0 t
  history5 : H5 t < R0 t
  oldW : W t ≤ R0 t
  oldBranches : ∀ m ∈ Finset.Icc 1 31,
    branchLicense ((oldBranchCell p).descending m) (R0 t) (subsetSum m t)
  clipAboveAscending : ascending33 t < clippedCap t
  ascendingNotLicensed : descending33 t < ascending33 t-eta
  improvement : R0 t < descendingNewCap t
  aboveHalf : 1/2 < descendingNewCap t
  selectedAscending : descendingNewCap t < ascending33 t
  selectedDescending : descendingNewCap t < descending33 t
  fullSquares : ∀ j : Fin 6, fullSquare j t < descendingNewCap t
  remainingSquares : ∀ j : Fin 6, bit 33 j.val = false →
    remainingSquare 33 j t < descendingNewCap t
  oldArgument : t 5 < R0 t-S6 t
  newArgument : descendingNewCap t-S6 t < 3*t 5

theorem PhysicalSource.coordinates_pos {p : Pattern} {t : Physical}
    (h : PhysicalSource p t) : ∀ i : Fin 6, 0 < t i := by
  intro i
  fin_cases i <;> linarith [h.rpos,h.order.1,h.order.2.1,h.order.2.2.1,
    h.order.2.2.2.1,h.order.2.2.2.2]

theorem PhysicalSource.old31_tent_upper {p : Pattern} {t : Physical}
    (h : PhysicalSource p t) (m : ℕ) (hm : m ∈ Finset.Icc 1 31) :
    tent (subsetSum m t) ≤ R0 t := branchLicense_sound (h.oldBranches m hm)

/-- Moving a subset by the same positive last-prime exponent increases
its tent by at most r/2. This applies to every selected original mask,
including mask50; it does not silently check only singleton33. -/
theorem tent_add_last_le (s r : ℝ) (hr : 0 ≤ r) :
    tent (s+r) ≤ tent s+r/2 := by
  unfold tent
  by_cases h : (1+s)/2 ≤ 57/64-3*s/2
  · rw [min_eq_left h]
    have hm := min_le_left ((1+(s+r))/2) (57/64-3*(s+r)/2)
    linarith
  · rw [min_eq_right (le_of_lt (lt_of_not_ge h))]
    have hm := min_le_right ((1+(s+r))/2) (57/64-3*(s+r)/2)
    linarith

def firstFiveSelectedMask (c : Cell) : ℕ := c.selectedMask % 32

theorem firstFiveSelectedMask_mem (c : Cell) :
    firstFiveSelectedMask c ∈ Finset.Icc 1 31 := by
  cases c <;> norm_num [firstFiveSelectedMask,Cell.selectedMask]

theorem all11_selected_sum_split (c : Cell) (t : Physical) :
    selectedSum c.selectedMask t = subsetSum (firstFiveSelectedMask c) t+t 5 := by
  cases c <;> norm_num [firstFiveSelectedMask,Cell.selectedMask,selectedSum,subsetSum,bit,
    Fin.sum_univ_succ] <;> ring

theorem PhysicalSource.all11_selected_tent_upper {p : Pattern} {t : Physical}
    (h : PhysicalSource p t) (c : Cell) :
    tent (selectedSum c.selectedMask t) ≤ ascending33 t := by
  rw [all11_selected_sum_split]
  calc
    _ ≤ tent (subsetSum (firstFiveSelectedMask c) t)+t 5/2 := tent_add_last_le _ _ h.rpos.le
    _ ≤ R0 t+t 5/2 := add_le_add_right
      (h.old31_tent_upper _ (firstFiveSelectedMask_mem c)) _
    _ = _ := by dsimp [R0,ascending33]; ring

/-- Every literal all11 source is excluded, including both pair families
and all selected masks33/34/50. For non-tent cells the clipped candidate
exceeds A33 but its selected licence is at most A33. For tent cells the
actual descending selector is opposite the old ascending-cell licence. -/
theorem PhysicalSource.not_any_originalEleven_cell {p : Pattern} {t : Physical}
    (h : PhysicalSource p t) (c : Cell) : ¬PhysicalCell c t := by
  intro hc
  by_cases ht : c.family = .tent33
  · have hmask : c.selectedMask = 33 := by
      cases c <;> simp_all [Cell.family,Cell.selectedMask]
    have hsum : selectedSum 33 t = t 0+t 5 := by
      norm_num [selectedSum,bit,Fin.sum_univ_succ]
    have hd := hc.selectedDescending
    rw [newCap,if_pos ht,hmask,hsum] at hd
    change ascending33 t-eta < descending33 t at hd
    linarith [h.ascendingNotLicensed]
  · have hcap : newCap c t = clippedCap t := by simp only [newCap,if_neg ht]
    have hlicense : newCap c t < tent (selectedSum c.selectedMask t) :=
      lt_min hc.selectedAscending hc.selectedDescending
    have hb := h.all11_selected_tent_upper c
    rw [hcap] at hlicense
    linarith [h.clipAboveAscending]

/-- This statement reads the actual common constructor on the actual
history; it is stronger than merely observing that the source tag8 was
absent from a newly defined tag inventory. -/
theorem actual_constructor_sixth_eq_parent_on_descending_source
    (d : OriginalData) (N : ℝ) (pre : List ℕ) (p : Pattern)
    (h : PhysicalSource p (primeHistoryLogCoordinates N 6 pre)) :
    lambda6 d N pre = actualParent5 d N pre := by
  apply lambda6_eq_parent_of_no_eligible
  intro c hc he
  exact h.not_any_originalEleven_cell c he.2.1

/-- Exact current-sixth-change profile at the same original descending
source. A previously higher fifth parent is NOT declared equal to R0. -/
theorem actual_constructor_sixth_profile_zero_on_descending_source
    (d : OriginalData) (N : ℝ) (pre : List ℕ) (p : Pattern)
    (h : PhysicalSource p (primeHistoryLogCoordinates N 6 pre)) :
    primeBoxInitialSavingProfile (actualParent5 d N pre) (lambda6 d N pre)
      (primeHistoryLogCoordinates N 6 pre) = 0 := by
  rw [actual_constructor_sixth_eq_parent_on_descending_source d N pre p h]
  simp [primeBoxInitialSavingProfile]

/-- The missing source's OWN physical cap has the original strict Theta
range. This is no assertion that the current constructor selects it. -/
theorem PhysicalSource.newCap_lt_originalTheta {p : Pattern} {t : Physical}
    (h : PhysicalSource p t) : descendingNewCap t < (299/500 : ℝ) := by
  have ha := h.selectedAscending
  have hd := h.selectedDescending
  dsimp [ascending33,descending33] at ha hd
  have hbound : descendingNewCap t < (153/256 : ℝ) := by linarith
  exact hbound.trans (by norm_num)

def archivedKernel (t : Physical) : ℝ :=
  primeBoxInitialSavingProfile (R0 t) (descendingNewCap t) t/coordinateProduct t

/-- Exact four-normalized source profile from the frozen factor program;
there is no Chen quarter and no permutation or ordering factorial. -/
theorem archivedKernel_eq_literal_factor_kernel (t : Physical) :
    archivedKernel t = 4*(descendingNewCap t-R0 t)/(∏ i,sourceFactors t i) := by
  rw [archivedKernel,sourceFactors_product]
  unfold primeBoxInitialSavingProfile
  rw [←S6_eq_sum t,div_div]

theorem PhysicalSource.sourceFactors_pos {p : Pattern} {t : Physical}
    (h : PhysicalSource p t) : ∀ i : Fin 8, 0 < sourceFactors t i := by
  have hR : 0 < R0 t-S6 t := h.rpos.trans h.oldArgument
  have hM : 0 < descendingNewCap t-S6 t := by linarith [h.improvement]
  intro i
  fin_cases i <;> simp only [sourceFactors,Matrix.cons_val_zero,Matrix.cons_val_succ] <;>
    first | exact hR | exact hM | exact h.coordinates_pos _

theorem PhysicalSource.archivedKernel_pos {p : Pattern} {t : Physical}
    (h : PhysicalSource p t) : 0 < archivedKernel t := by
  have hR : 0 < R0 t-S6 t := h.rpos.trans h.oldArgument
  have hM : 0 < descendingNewCap t-S6 t := by linarith [h.improvement]
  have hprod : 0 < coordinateProduct t := Finset.prod_pos (fun i _ => h.coordinates_pos i)
  unfold archivedKernel primeBoxInitialSavingProfile
  rw [←S6_eq_sum t]
  exact div_pos (div_pos (mul_pos (by norm_num) (sub_pos.mpr h.improvement))
    (mul_pos hR hM)) hprod

/-- This is a local archived-versus-current-STAGE discrepancy, not a
claim that the whole manuscript's telescoping density loses this amount.
A correct full22 caller must account for the actual missing action/owner
or prove an earlier same-source absorption with its exact gain difference. -/
theorem descending_source_archived_profile_not_current_sixth_profile
    (d : OriginalData) (N : ℝ) (pre : List ℕ) (p : Pattern)
    (h : PhysicalSource p (primeHistoryLogCoordinates N 6 pre)) :
    primeBoxInitialSavingProfile (actualParent5 d N pre) (lambda6 d N pre)
      (primeHistoryLogCoordinates N 6 pre) /
        coordinateProduct (primeHistoryLogCoordinates N 6 pre) <
      archivedKernel (primeHistoryLogCoordinates N 6 pre) := by
  rw [actual_constructor_sixth_profile_zero_on_descending_source d N pre p h,zero_div]
  exact h.archivedKernel_pos

end
end ImbalancedChen.P5Z.OriginalDescending33ActualOmission
