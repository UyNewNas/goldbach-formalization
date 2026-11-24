import ImbalancedChen.P2Winner9SeedVertexAnalyticGuards
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-! The original Winner9 minorant cell and its affine source walls. -/
namespace ImbalancedChen.P2Winner9OriginalSourceGates

noncomputable section

open Set MeasureTheory
open scoped BigOperators
open P2Winner9CompleteSeedVertices
open P2Winner9SeedVertexAnalyticGuards (VertexIndex originalPoint)
open P2Winner9SelectedRowRealJacobian P2Winner9SelectedRowAnalyticCaps
open P2Winner9PhysicalAffineTransfer P2Winner9PhysicalVertexInterpolation
open P2Winner9BarycentricMixedDegreeOne

structure Row where
  constant : ℚ
  coefficient : Fin 8 → ℚ
  deriving DecidableEq

def Row.evalQ (r : Row) (x : Fin 8 → ℚ) : ℚ :=
  r.constant + ∑ j, r.coefficient j * x j
def Row.eval (r : Row) (x : Ambient) : ℝ :=
  r.constant + ∑ j, (r.coefficient j : ℝ) * x j
def Row.const (c : ℚ) : Row := ⟨c, fun _ => 0⟩
def Row.coord (j : Fin 8) : Row := ⟨0, fun k => if k = j then 1 else 0⟩
def Row.add (r s : Row) : Row :=
  ⟨r.constant + s.constant, fun j => r.coefficient j + s.coefficient j⟩
def Row.sub (r s : Row) : Row :=
  ⟨r.constant - s.constant, fun j => r.coefficient j - s.coefficient j⟩
def Row.scale (c : ℚ) (r : Row) : Row :=
  ⟨c * r.constant, fun j => c * r.coefficient j⟩
def Row.sum (P : Fin 8 → Prop) [DecidablePred P] : Row :=
  ⟨0, fun j => if P j then 1 else 0⟩

@[simp] theorem Row.eval_cast (r : Row) (x : Fin 8 → ℚ) :
    r.eval (fun j => (x j : ℝ)) = (r.evalQ x : ℝ) := by
  simp [Row.eval, Row.evalQ]
@[simp] theorem Row.eval_sub (r s : Row) (x : Ambient) :
    (r.sub s).eval x = r.eval x - s.eval x := by
  simp [Row.eval, Row.sub, sub_mul, Finset.sum_sub_distrib]
  ring
@[simp] theorem Row.eval_add (r s : Row) (x : Ambient) :
    (r.add s).eval x = r.eval x + s.eval x := by
  simp [Row.eval, Row.add, add_mul, Finset.sum_add_distrib]
  ring
@[simp] theorem Row.eval_scale (c : ℚ) (r : Row) (x : Ambient) :
    (r.scale c).eval x = (c : ℝ) * r.eval x := by
  simp [Row.eval, Row.scale, Finset.mul_sum, mul_add, mul_assoc]
@[simp] theorem Row.eval_const (c : ℚ) (x : Ambient) :
    (Row.const c).eval x = (c : ℝ) := by simp [Row.eval, Row.const]
@[simp] theorem Row.eval_coord (j : Fin 8) (x : Ambient) :
    (Row.coord j).eval x = x j := by
  simp only [Row.eval, Row.coord, Rat.cast_zero, zero_add]
  rw [Finset.sum_eq_single j]
  · simp
  · intro k _ h
    simp [h]
  · simp

theorem Row.eval_vertexMap (r : Row) (v : Fin 9 → Ambient) (x : Ambient) :
    r.eval (vertexMap v x) = affine (fun k => r.eval (v k)) x := by
  simp only [Row.eval, vertexMap_coordinate, affine_add, affine_constant, affine_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  simp [affine, Finset.mul_sum, mul_assoc]

theorem Row.support_nonneg (r : Row) (v : RationalVertices)
    (hv : ∀ k, 0 ≤ r.evalQ (v k)) {x : Ambient} (hx : x ∈ sourceSupport v) :
    0 ≤ r.eval x := by
  rcases hx with ⟨y, hy, rfl⟩
  rw [Row.eval_vertexMap]
  apply affine_lower hy _ 0
  intro k
  change 0 ≤ r.eval (fun j => (v k j : ℝ))
  rw [Row.eval_cast]
  exact_mod_cast hv k

def Row.linearPart (r : Row) : Ambient →L[ℝ] ℝ :=
  ∑ j : Fin 8, (r.coefficient j : ℝ) • ContinuousLinearMap.proj j
theorem Row.eval_eq_affine (r : Row) (x : Ambient) :
    r.eval x = (r.constant : ℝ) + r.linearPart x := by
  simp only [Row.eval, Row.linearPart, sum_apply, smul_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul]
theorem Row.continuous (r : Row) : Continuous r.eval := by
  rw [show r.eval = (fun x => (r.constant : ℝ) + r.linearPart x) from
    funext r.eval_eq_affine]
  fun_prop

private def Row.zeroWall (r : Row) : AffineSubspace ℝ Ambient where
  carrier := {x | r.eval x = 0}
  smul_vsub_vadd_mem' := by
    intro t x y z hx hy hz
    change r.eval (t • (x - y) + z) = 0
    change r.eval x = 0 at hx
    change r.eval y = 0 at hy
    change r.eval z = 0 at hz
    simp only [Row.eval_eq_affine] at hx hy hz ⊢
    simp only [map_add, map_smul, map_sub]
    rw [show r.linearPart x = r.linearPart y by linarith]
    simpa [add_comm] using hz

/-- Every affine row with a nonzero value has a Lebesgue-null zero set. -/
theorem Row.zero_volume (r : Row) (h : ∃ x : Ambient, r.eval x ≠ 0) :
    volume {x | r.eval x = 0} = 0 := by
  change volume (r.zeroWall : Set Ambient) = 0
  apply Measure.addHaar_affineSubspace volume
  intro htop
  obtain ⟨x, hx⟩ := h
  apply hx
  change x ∈ r.zeroWall
  rw [htop]
  trivial

def ascending (r : Row) : Row := (Row.const (1/2)).add (r.scale (1/2))
def descending (r : Row) : Row := (Row.const (57/64)).sub (r.scale (3/2))
def maskRow (m : ℕ) : Row := Row.sum (fun j => Nat.testBit m j.val)

private theorem mask9_eq : maskRow 9 = (Row.coord 0).add (Row.coord 3) := by
  change Row.mk _ _ = Row.mk _ _
  congr 1
  · simp [Row.coord]
  · funext j
    fin_cases j <;> decide +kernel

private theorem mask6_eq : maskRow 6 = (Row.coord 1).add (Row.coord 2) := by
  change Row.mk _ _ = Row.mk _ _
  congr 1
  · simp [Row.coord]
  · funext j
    fin_cases j <;> decide +kernel

private theorem mask138_eq :
    maskRow 138 = ((Row.coord 1).add (Row.coord 3)).add (Row.coord 7) := by
  change Row.mk _ _ = Row.mk _ _
  congr 1
  · simp [Row.add, Row.coord]
  · funext j
    fin_cases j <;> decide +kernel

def prefixRow (j : Fin 8) : Row := Row.sum (fun k => k < j)
def selectedPrefixRow (j : Fin 8) : Row :=
  Row.sum (fun k => k < j ∧ ¬ Nat.testBit 138 k.val)
def R : Row := ascending ((Row.coord 0).add (Row.coord 3))
def B3 : Row := descending ((Row.coord 1).add (Row.coord 2))
def M : Row := (ascending (maskRow 138)).sub (Row.const (1/1000000))
def W : Row := (Row.const (153/256)).sub ((Row.coord 2).scale (3/8))
def S : Row := Row.sum (fun _ => True)

/-- The eight original navigation seed coordinates select the old planes. -/
def navigationSeed : Fin 8 → ℚ := fun j =>
  (![115365267465, 104500235252, 97721136227, 68922122738,
      55525244864, 46801972101, 28296601588, 21808164892] j : ℚ) / 10^12
def oldPlane (m : ℕ) : Row :=
  if (descending (maskRow m)).evalQ navigationSeed <
      (ascending (maskRow m)).evalQ navigationSeed
  then descending (maskRow m) else ascending (maskRow m)

private theorem oldPlane9_eq : R = oldPlane 9 := by
  have h : ¬ (descending (maskRow 9)).evalQ navigationSeed <
      (ascending (maskRow 9)).evalQ navigationSeed := by decide +kernel
  rw [oldPlane, if_neg h]
  simp [R, mask9_eq]

abbrev ProperOld := {m : Fin 63 // m.val ≠ 8}
abbrev ComplementSlot := {j : Fin 8 // j.val ≠ 1 ∧ j.val ≠ 3 ∧ j.val ≠ 7}
inductive Gate
  | largest | third | eighth
  | order (j : Fin 7)
  | history (j : Fin 4)
  | minorantGap | winnerSide | thirdSide | oldW
  | oldSubset (m : ProperOld)
  | improvement | selectedDescending
  | fullSquare (j : Fin 8)
  | complementSquare (j : ComplementSlot)
  | oldResidual | newResidual
  deriving DecidableEq, Fintype

def gate : Gate → Row
  | .largest => (Row.const (25/128)).sub (Row.coord 0)
  | .third => (Row.coord 2).sub (Row.const (1/100))
  | .eighth => (Row.coord 7).sub (Row.const (53/13824))
  | .order j => (Row.coord j.castSucc).sub (Row.coord j.succ)
  | .history j =>
      let k : Fin 8 := ⟨2*j.val, by omega⟩
      B3.sub ((prefixRow k).add ((Row.coord k).scale 3))
  | .minorantGap => R.sub B3
  | .winnerSide => (descending ((Row.coord 0).add (Row.coord 3))).sub R
  | .thirdSide => (ascending ((Row.coord 1).add (Row.coord 2))).sub B3
  | .oldW => R.sub W
  | .oldSubset m => R.sub (oldPlane (m.val.val+1))
  | .improvement => M.sub R
  | .selectedDescending =>
      ((descending (maskRow 138)).sub (Row.const (1/1000000))).sub M
  | .fullSquare j => M.sub ((prefixRow j).add ((Row.coord j).scale 2))
  | .complementSquare j => M.sub
      ((maskRow 138).add ((selectedPrefixRow j.val).add ((Row.coord j.val).scale 2)))
  | .oldResidual => (R.sub S).sub (Row.coord 7)
  | .newResidual => (S.add ((Row.coord 7).scale 3)).sub M

private def gateGuardAt (n : ℕ) : Prop :=
  ∀ g : Gate, 0 ≤ (gate g).evalQ coordinates[n]!

private def chunkSize (c : Fin 26) : ℕ := min 8 (201 - 8 * c.val)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem gate_guards_chunk (c : Fin 26) : ∀ i : Fin (chunkSize c),
    gateGuardAt (8 * c.val + i.val) := by
  fin_cases c <;> unfold gateGuardAt chunkSize <;> decide +kernel

private theorem gate_guards (v : VertexIndex) : ∀ g : Gate,
    0 ≤ (gate g).evalQ (originalPoint v) := by
  change gateGuardAt v.val
  let c : Fin 26 := ⟨v.val / 8, by have := v.isLt; omega⟩
  have he : 8 * c.val + v.val % 8 = v.val := Nat.div_add_mod v.val 8
  have hi : v.val % 8 < chunkSize c := by
    apply Nat.lt_min.mpr
    exact ⟨Nat.mod_lt _ (by decide), by have := v.isLt; omega⟩
  exact he ▸ gate_guards_chunk c ⟨v.val % 8, hi⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
/-- The 97 proper affine gates and their original vertex inequalities. -/
theorem original_vertex_source_guards :
    Fintype.card Gate = 97 ∧
    (∀ g : Gate, ∃ j : Fin 8, (gate g).coefficient j ≠ 0) ∧
    (∀ v : VertexIndex, ∀ g : Gate, 0 ≤ (gate g).evalQ (originalPoint v)) ∧
    R = oldPlane 9 ∧ M = (ascending (maskRow 138)).sub (Row.const (1/1000000)) :=
  ⟨by decide +kernel, by decide +kernel, gate_guards, oldPlane9_eq, rfl⟩

/-- The original strict minorant cell; source coordinates, mask138 and
history are independent of the simplex lists. -/
def originalPhysicalSource : Set Ambient := {x | ∀ g : Gate, 0 < (gate g).eval x}
def originalClosedSource : Set Ambient := {x | ∀ g : Gate, 0 ≤ (gate g).eval x}
def sourceWalls : Set Ambient := ⋃ g : Gate, {x | (gate g).eval x = 0}

theorem all_supports_in_closed_source (v : RationalVertices) (ids : Fin 9 → VertexIndex)
    (h : ∀ i, v i = originalPoint (ids i)) : sourceSupport v ⊆ originalClosedSource := by
  intro x hx g
  apply Row.support_nonneg (gate g) v _ hx
  intro k
  rw [h k]
  exact original_vertex_source_guards.2.2.1 _ g

theorem gate_zero_volume (g : Gate) : volume {x | (gate g).eval x = 0} = 0 := by
  apply Row.zero_volume
  obtain ⟨j, hj⟩ := original_vertex_source_guards.2.1 g
  by_cases hc : (gate g).constant = 0
  · refine ⟨Pi.single j 1, ?_⟩
    simpa [Row.eval, hc, Pi.single_apply] using
      (show ((gate g).coefficient j : ℝ) ≠ 0 by exact_mod_cast hj)
  · refine ⟨0, ?_⟩
    simpa [Row.eval] using (show ((gate g).constant : ℝ) ≠ 0 by exact_mod_cast hc)

theorem sourceWalls_null : volume sourceWalls = 0 := by
  exact measure_iUnion_null (fun g => gate_zero_volume g)

theorem sourceWalls_measurable : MeasurableSet sourceWalls := by
  exact MeasurableSet.iUnion (fun g =>
    (isClosed_eq (gate g).continuous continuous_const).measurableSet)

theorem originalClosedSource_measurable : MeasurableSet originalClosedSource := by
  unfold originalClosedSource
  simp only [Set.ofPred_forall]
  exact MeasurableSet.iInter (fun g =>
    (isClosed_le continuous_const (gate g).continuous).measurableSet)

theorem originalPhysicalSource_measurable : MeasurableSet originalPhysicalSource := by
  unfold originalPhysicalSource
  simp only [Set.ofPred_forall]
  exact MeasurableSet.iInter (fun g =>
    (isOpen_lt continuous_const (gate g).continuous).measurableSet)

/-- Removing the null source walls gives strict source membership. -/
theorem support_off_walls_in_original_source (v : RationalVertices) (ids : Fin 9 → VertexIndex)
    (h : ∀ i, v i = originalPoint (ids i)) :
    sourceSupport v \ sourceWalls ⊆ originalPhysicalSource := by
  rintro x ⟨hx, hw⟩ g
  have hge := all_supports_in_closed_source v ids h hx g
  have hne : (gate g).eval x ≠ 0 := fun he =>
    hw (mem_iUnion.mpr ⟨g, he⟩)
  exact lt_of_le_of_ne hge (Ne.symm hne)

theorem R_is_original (x : Ambient) : R.eval x = physicalR x := by
  simp [R, ascending, physicalR]
  ring

theorem M_is_original (x : Ambient) : M.eval x = physicalM x := by
  simp [M, ascending, mask138_eq, physicalM]
  ring

/-- The original tent takes the minimum of its two affine planes. -/
def originalTent (m : ℕ) (x : Ambient) : ℝ :=
  min ((ascending (maskRow m)).eval x) ((descending (maskRow m)).eval x)

theorem chosen_plane_dominates_tent (m : ℕ) (x : Ambient) :
    originalTent m x ≤ (oldPlane m).eval x := by
  unfold oldPlane
  split_ifs
  · exact min_le_right _ _
  · exact min_le_left _ _

theorem original_mask_identities :
    R = ascending (maskRow 9) ∧ B3 = descending (maskRow 6) := by
  simp [R, B3, mask9_eq, mask6_eq]

/-- The original winner dominates W and all 63 old tents and attains mask9. -/
theorem source_original_raw_sixth_winner {x : Ambient} (hx : x ∈ originalPhysicalSource) :
    W.eval x < physicalR x ∧
    (∀ m : Fin 63, originalTent (m.val+1) x ≤ physicalR x) ∧
    originalTent 9 x = physicalR x := by
  have hs : R.eval x < (descending ((Row.coord 0).add (Row.coord 3))).eval x := by
    have h := hx .winnerSide
    simpa [gate] using h
  have hdesc : descending ((Row.coord 0).add (Row.coord 3)) = descending (maskRow 9) := by
    rw [mask9_eq]
  have hwin : originalTent 9 x = R.eval x := by
    unfold originalTent
    rw [← original_mask_identities.1]
    exact min_eq_left (by simpa only [hdesc] using hs.le)
  refine ⟨?_, ?_, by simpa only [R_is_original] using hwin⟩
  · have h := hx .oldW
    simpa [gate, R_is_original] using h
  · intro m
    by_cases hm : m.val = 8
    · have he : m.val+1 = 9 := by omega
      simpa only [he, hwin, R_is_original] using (le_refl (physicalR x))
    · have h := hx (.oldSubset ⟨m, hm⟩)
      have hp : (oldPlane (m.val+1)).eval x < physicalR x := by
        simpa [gate, R_is_original] using h
      exact (chosen_plane_dominates_tent (m.val+1) x).trans hp.le

/-- B3 agrees with the original mask6 third tent on the strict cell. -/
theorem source_original_third_minorant {x : Ambient} (hx : x ∈ originalPhysicalSource) :
    originalTent 6 x = B3.eval x := by
  have h := hx .thirdSide
  have ha : ascending ((Row.coord 1).add (Row.coord 2)) = ascending (maskRow 6) := by
    rw [mask6_eq]
  have hs : B3.eval x ≤ (ascending (maskRow 6)).eval x := by
    have hp : B3.eval x < (ascending (maskRow 6)).eval x := by
      simpa [gate, ha] using h
    exact hp.le
  unfold originalTent
  rw [← original_mask_identities.2]
  exact min_eq_right hs

end
end ImbalancedChen.P2Winner9OriginalSourceGates
