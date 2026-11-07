import ImbalancedChen.P1OriginalFourthIntegerGapSemantics

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED / ZERO_CREDIT.

Symbolic original fourth source integer cube, ALL full/selected-square
gates, and row domain tests, using D=32*204800 from the gap module.
Source certify_fourth_prefix_stronger.py SHA256
25069573985d30beae59a1a2a89ddeb79e56f696e78a5fae5153de0bb8bd378a.
Every difference is formed before lower endpoint evaluation. Original
OLD ordering and mask processing slots are unchanged. No actual row test,
numerical replay or machine-int64 implementation is executed or certified.
-/

namespace ImbalancedChen.P1OriginalFourthIntegerCubeGateSemantics
open P2OriginalFourthCapProducerInterface
open P1OriginalPrefixRowDecodeSoundness
open P1OriginalFourthIntegerGapSemantics
open scoped BigOperators

noncomputable section
open scoped Classical

def sourceCube : IntegerAffine := ⟨0, ![32,32,96,0]⟩
def sourceHalfGate : IntegerAffine := ⟨3276800, fun _ => 0⟩

/-- Source full gate: 32*(1_{i<j}+2*1_{i=j}). -/
def sourceFullGate (j : Fin 4) : IntegerAffine :=
  ⟨0, fun i => 32 * ((if i < j then 1 else 0) + (if i = j then 2 else 0))⟩

/-- Source before[] records exactly earlier unselected processing slots. -/
def sourceSelectedGate (I : Finset (Fin 4)) (j : Fin 4) : IntegerAffine :=
  ⟨0, fun i => 32 * ((if i ∈ I then 1 else 0) +
    (if i < j ∧ i ∉ I then 1 else 0) + (if i = j then 2 else 0))⟩

theorem sourceCube_toAffine : sourceCube.toAffine = oldCube := by
  apply congrArg₂ Affine.mk
  · norm_num [sourceCube, IntegerAffine.toAffine, oldCube]
  · funext i
    fin_cases i <;> norm_num [sourceCube, IntegerAffine.toAffine, oldCube]

theorem sourceHalfGate_toAffine : sourceHalfGate.toAffine = halfGate := by
  apply congrArg₂ Affine.mk
  · norm_num [sourceHalfGate, IntegerAffine.toAffine, halfGate]
  · funext i
    norm_num [sourceHalfGate, IntegerAffine.toAffine, halfGate]

theorem sourceFullGate_toAffine (j : Fin 4) : (sourceFullGate j).toAffine = fullGate j := by
  apply congrArg₂ Affine.mk
  · norm_num [sourceFullGate, IntegerAffine.toAffine, fullGate]
  · funext i
    by_cases hlt : i < j <;> by_cases heq : i = j <;>
      norm_num [sourceFullGate, IntegerAffine.toAffine, fullGate, hlt, heq]

theorem sourceSelectedGate_toAffine (I : Finset (Fin 4)) (j : Fin 4) :
    (sourceSelectedGate I j).toAffine = selectedGate I j := by
  apply congrArg₂ Affine.mk
  · norm_num [sourceSelectedGate, IntegerAffine.toAffine, selectedGate]
  · funext i
    by_cases hm : i ∈ I <;> by_cases hb : i < j ∧ i ∉ I <;> by_cases heq : i = j <;>
      norm_num [sourceSelectedGate, IntegerAffine.toAffine, selectedGate, hm, hb, heq]

/-- Source max-old/min-oldline cube margin in the literal Python OLD order. -/
def integerOldCubeSlack (raw : FourthWireRow) : ℤ :=
  Finset.univ.sup' (show (Finset.univ : Finset (Fin 6)).Nonempty from ⟨0, by simp⟩)
    (fun j => min (((programOldPiece j false).sub sourceCube).lower raw.lo raw.hi)
      (((programOldPiece j true).sub sourceCube).lower raw.lo raw.hi))

def integerCubeRows (raw : FourthWireRow) : Prop :=
  ∃ j : Fin 6, (0 : ℤ) <
    min (((programOldPiece j false).sub sourceCube).lower raw.lo raw.hi)
      (((programOldPiece j true).sub sourceCube).lower raw.lo raw.hi)

def rationalCubeRows (raw : FourthWireRow) : Prop :=
  ∃ j : Fin 6, (0 : ℚ) <
    min (((oldPiece j false).sub oldCube).lower raw.toProducerRow.lower raw.toProducerRow.upper)
      (((oldPiece j true).sub oldCube).lower raw.toProducerRow.lower raw.toProducerRow.upper)

theorem integerOldCubeSlack_pos_iff (raw : FourthWireRow) :
    0 < integerOldCubeSlack raw ↔ integerCubeRows raw := by
  constructor
  · intro h
    obtain ⟨j, _hj, hj⟩ := (Finset.lt_sup'_iff _).mp h
    exact ⟨j, hj⟩
  · rintro ⟨j, hj⟩
    exact (Finset.lt_sup'_iff _).mpr ⟨j, Finset.mem_univ _, hj⟩

theorem cube_piece_positive_iff (raw : FourthWireRow) (j : Fin 6) :
    (0 : ℚ) <
      min (((oldPiece j false).sub oldCube).lower raw.toProducerRow.lower raw.toProducerRow.upper)
        (((oldPiece j true).sub oldCube).lower raw.toProducerRow.lower raw.toProducerRow.upper) ↔
    (0 : ℤ) < min (((sourceOld j false).sub sourceCube).lower raw.lo raw.hi)
      (((sourceOld j true).sub sourceCube).lower raw.lo raw.hi) := by
  have h0 := lower_positive_iff ((sourceOld j false).sub sourceCube) raw.lo raw.hi
  have h1 := lower_positive_iff ((sourceOld j true).sub sourceCube) raw.lo raw.hi
  simp only [toAffine_sub, sourceOld_toAffine, sourceCube_toAffine] at h0 h1
  simp only [lt_min_iff]
  exact and_congr h0 h1

theorem integerCubeRows_iff (raw : FourthWireRow) :
    integerCubeRows raw ↔ rationalCubeRows raw := by
  constructor
  · rintro ⟨j, hj⟩
    exact ⟨pythonToCommon j, (cube_piece_positive_iff raw (pythonToCommon j)).mpr hj⟩
  · rintro ⟨j, hj⟩
    refine ⟨commonToPython j, ?_⟩
    have h := (cube_piece_positive_iff raw j).mp hj
    simpa only [programOldPiece, pythonToCommon_commonToPython] using h

/-- All source gate numerators, including every permitted selected gate. -/
def integerGateRows (raw : FourthWireRow) : Prop :=
  (∀ side : Bool, (0 : ℤ) <
    ((sourceTent raw.toProducerRow.selected side).sub sourceHalfGate).lower raw.lo raw.hi) ∧
  (∀ side : Bool, ∀ j : Fin 4, (0 : ℤ) <
    ((sourceTent raw.toProducerRow.selected side).sub (sourceFullGate j)).lower raw.lo raw.hi) ∧
  (∀ side : Bool, ∀ j : Fin 4, j ∉ raw.toProducerRow.selected → (0 : ℤ) <
    ((sourceTent raw.toProducerRow.selected side).sub
      (sourceSelectedGate raw.toProducerRow.selected j)).lower raw.lo raw.hi)

def rationalGateRows (raw : FourthWireRow) : Prop :=
  (∀ side : Bool, (0 : ℚ) < ((tentPlane raw.toProducerRow.selected side).sub halfGate).lower
    raw.toProducerRow.lower raw.toProducerRow.upper) ∧
  (∀ side : Bool, ∀ j : Fin 4, (0 : ℚ) <
    ((tentPlane raw.toProducerRow.selected side).sub (fullGate j)).lower
      raw.toProducerRow.lower raw.toProducerRow.upper) ∧
  (∀ side : Bool, ∀ j : Fin 4, j ∉ raw.toProducerRow.selected → (0 : ℚ) <
    ((tentPlane raw.toProducerRow.selected side).sub (selectedGate raw.toProducerRow.selected j)).lower
      raw.toProducerRow.lower raw.toProducerRow.upper)

theorem half_gate_positive_iff (raw : FourthWireRow) (side : Bool) :
    (0 : ℚ) < ((tentPlane raw.toProducerRow.selected side).sub halfGate).lower
      raw.toProducerRow.lower raw.toProducerRow.upper ↔
    (0 : ℤ) < ((sourceTent raw.toProducerRow.selected side).sub sourceHalfGate).lower raw.lo raw.hi := by
  simpa only [toAffine_sub, sourceTent_toAffine, sourceHalfGate_toAffine] using
    (lower_positive_iff ((sourceTent raw.toProducerRow.selected side).sub sourceHalfGate) raw.lo raw.hi)

theorem full_gate_positive_iff (raw : FourthWireRow) (side : Bool) (j : Fin 4) :
    (0 : ℚ) < ((tentPlane raw.toProducerRow.selected side).sub (fullGate j)).lower
      raw.toProducerRow.lower raw.toProducerRow.upper ↔
    (0 : ℤ) < ((sourceTent raw.toProducerRow.selected side).sub (sourceFullGate j)).lower raw.lo raw.hi := by
  simpa only [toAffine_sub, sourceTent_toAffine, sourceFullGate_toAffine] using
    (lower_positive_iff ((sourceTent raw.toProducerRow.selected side).sub (sourceFullGate j)) raw.lo raw.hi)

theorem selected_gate_positive_iff (raw : FourthWireRow) (side : Bool) (j : Fin 4) :
    (0 : ℚ) <
      ((tentPlane raw.toProducerRow.selected side).sub (selectedGate raw.toProducerRow.selected j)).lower
        raw.toProducerRow.lower raw.toProducerRow.upper ↔
    (0 : ℤ) < ((sourceTent raw.toProducerRow.selected side).sub
      (sourceSelectedGate raw.toProducerRow.selected j)).lower raw.lo raw.hi := by
  simpa only [toAffine_sub, sourceTent_toAffine, sourceSelectedGate_toAffine] using
    (lower_positive_iff ((sourceTent raw.toProducerRow.selected side).sub
      (sourceSelectedGate raw.toProducerRow.selected j)) raw.lo raw.hi)

theorem integerGateRows_iff (raw : FourthWireRow) :
    integerGateRows raw ↔ rationalGateRows raw := by
  simp only [integerGateRows, rationalGateRows, half_gate_positive_iff,
    full_gate_positive_iff, selected_gate_positive_iff]

theorem integerGateRows_wholeBoxGates (raw : FourthWireRow) (h : integerGateRows raw) :
    WholeBoxGateRows raw.toProducerRow.selected raw.toProducerRow.lower raw.toProducerRow.upper := by
  have hq := (integerGateRows_iff raw).mp h
  refine ⟨?_, ?_, ?_⟩
  · intro side
    exact_mod_cast hq.1 side
  · intro side j
    exact_mod_cast hq.2.1 side j
  · intro side j hj
    exact_mod_cast hq.2.2 side j hj

/-- Original per-row mask, width, order and lattice-coordinate cut tests.
Dyadic refinement/disjointness of the full family is a separate predicate. -/
def integerDomainRows (raw : FourthWireRow) : Prop :=
  9 ≤ raw.mask ∧ raw.mask ≤ 15 ∧
  (∀ i, raw.lo i < raw.hi i) ∧
  (∀ i : Fin 3, raw.hi i.succ ≤ raw.lo i.castSucc) ∧
  3072 ≤ raw.lo 3 ∧ raw.hi 0 ≤ 39936

def rationalDomainRows (raw : FourthWireRow) : Prop :=
  9 ≤ raw.toProducerRow.mask ∧ raw.toProducerRow.mask ≤ 15 ∧
  (∀ i, raw.toProducerRow.lo i < raw.toProducerRow.hi i) ∧
  (∀ i : Fin 3, raw.toProducerRow.hi i.succ ≤ raw.toProducerRow.lo i.castSucc) ∧
  (3 / 200 : ℚ) ≤ raw.toProducerRow.lower 3 ∧ raw.toProducerRow.upper 0 ≤ (39 / 200 : ℚ)

theorem integerDomainRows_iff (raw : FourthWireRow) :
    integerDomainRows raw ↔ rationalDomainRows raw := by
  constructor
  · rintro ⟨hm0, hm1, hw, ho, hlo, hhi⟩
    refine ⟨hm0, hm1, hw, ho, ?_, ?_⟩
    · change (3 / 200 : ℚ) ≤ (raw.lo 3 : ℚ) / 204800
      have : (3072 : ℚ) ≤ (raw.lo 3 : ℚ) := by exact_mod_cast hlo
      linarith
    · change (raw.hi 0 : ℚ) / 204800 ≤ (39 / 200 : ℚ)
      have : (raw.hi 0 : ℚ) ≤ 39936 := by exact_mod_cast hhi
      linarith
  · rintro ⟨hm0, hm1, hw, ho, hlo, hhi⟩
    refine ⟨hm0, hm1, hw, ho, ?_, ?_⟩
    · change (3 / 200 : ℚ) ≤ (raw.lo 3 : ℚ) / 204800 at hlo
      have : (3072 : ℚ) ≤ (raw.lo 3 : ℚ) := by linarith
      exact_mod_cast this
    · change (raw.hi 0 : ℚ) / 204800 ≤ (39 / 200 : ℚ) at hhi
      have : (raw.hi 0 : ℚ) ≤ 39936 := by linarith
      exact_mod_cast this

end
end ImbalancedChen.P1OriginalFourthIntegerCubeGateSemantics
