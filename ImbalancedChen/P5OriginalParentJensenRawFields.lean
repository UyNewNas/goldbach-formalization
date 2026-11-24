import ImbalancedChen.P5OriginalParentJensenDirectedLog
import ImbalancedChen.P1HistoricalFifthIndexedOwnerArchive
import ImbalancedChen.P1HistoricalFifthTypedBaseGeometry

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The old Jensen term is reconstructed from the ORIGINAL ten-column row,
including its stored d/A/B, through adaptive.exact_term called with the
Jensen producer's 32-fold rescaling.  It is NOT reconstructed from any
child d/A/B, and it is NOT the later stored Jensen/Taylor maximum.

The finite scalar checks are supplied in a separate source.  They are
integer/rational equalities and range checks, never real integral bounds.
-/
namespace ImbalancedChen.P5OriginalParentJensenRawFields
open scoped BigOperators
open P1OriginalPrefixRowDecodeSoundness
open P5OriginalParentJensenDirectedLog
open ImbalancedChen.Certificates.P2DirectedLogRounding

def originalParentH (raw : FifthWireRow) : ℤ :=
  32 * (32 * (raw.lo 4 + 1))

def originalParentC (raw : FifthWireRow) : ℤ :=
  originalParentH raw * raw.ratioA - raw.vertexGapSum * raw.ratioB

def originalParentZ (raw : FifthWireRow) : ℤ :=
  raw.vertexGapSum * raw.ratioB

def originalParentD (raw : FifthWireRow) : ℤ :=
  2 * originalParentH raw * (raw.ratioA - raw.ratioB) - originalParentZ raw

def originalParentRN (raw : FifthWireRow) : ℤ :=
  let Z := originalParentZ raw
  let D := originalParentD raw
  2 * Z * (15 * D ^ 4 + 5 * Z ^ 2 * D ^ 2 + 3 * Z ^ 4)

def originalParentRD (raw : FifthWireRow) : ℤ := 15 * originalParentD raw ^ 5

def originalParentY (raw : FifthWireRow) : ℤ :=
  originalParentC raw - 2 * originalParentH raw * raw.ratioB

def originalParentLN (raw : FifthWireRow) : ℤ :=
  let Y := originalParentY raw
  let C := originalParentC raw
  2 * Y * (3 * C ^ 2 - 2 * Y ^ 2)

def originalParentLD (raw : FifthWireRow) : ℤ :=
  3 * originalParentC raw * (originalParentC raw ^ 2 - originalParentY raw ^ 2)

def originalParentDN (raw : FifthWireRow) : ℤ :=
  raw.ratioB * (originalParentC raw * originalParentRN raw * originalParentLD raw -
    raw.vertexGapSum * raw.ratioB * originalParentLN raw * originalParentRD raw)

def originalParentDD (raw : FifthWireRow) : ℤ :=
  originalParentC raw * raw.ratioA * originalParentRD raw * originalParentLD raw

/-- Literal rescaled source numerator, before the Q80 integer division. -/
def originalParentNumerator (raw : FifthWireRow) : ℤ :=
  4 * (32 * raw.grid) *
    (∏ k : Fin 5, (32 * (raw.lo k + 1) - 32 * raw.lo k)) * originalParentDN raw

def originalParentDenominator (raw : FifthWireRow) : ℤ :=
  (∏ k : Fin 5, 32 * (raw.lo k + 1)) *
    (32 * (raw.lo 4 + 1)) * originalParentDD raw

def originalParentJensenFloorZ (raw : FifthWireRow) : ℤ :=
  (2 : ℤ) ^ 80 * originalParentNumerator raw / originalParentDenominator raw

def originalParentJensenFloorQ (raw : FifthWireRow) : ℚ :=
  (originalParentJensenFloorZ raw : ℚ) / dyadicScale 80

def parentBQ (raw : FifthWireRow) : ℚ := (raw.ratioA : ℚ) / (raw.ratioB : ℚ)

def parentEQ (raw : FifthWireRow) : ℚ :=
  (raw.vertexGapSum : ℚ) / (1024 * ((raw.lo 4 : ℚ) + 1))

def parentPrefactorQ (raw : FifthWireRow) : ℚ :=
  (4 * (raw.grid : ℚ)) /
    ((∏ k : Fin 5, ((raw.lo k : ℚ) + 1)) * ((raw.lo 4 : ℚ) + 1))

def parentJensenRationalQ (raw : FifthWireRow) : ℚ :=
  parentPrefactorQ raw * parentDirectedQ (parentBQ raw) (parentEQ raw)

/-- Precisely the finite input layer still missing from the previously
opaque original d/A/B fields.  Floor equality is rational arithmetic,
not the desired integral inequality, and no stored Taylor field occurs. -/
def ParentScalarFacts (raw : FifthWireRow) : Prop :=
  0 < raw.ratioB ∧ 0 < raw.vertexGapSum ∧
  2 < parentBQ raw ∧ parentBQ raw ≤ 4 ∧
  0 ≤ parentEQ raw ∧ parentEQ raw ≤ parentBQ raw - 2 ∧
  0 ≤ parentPrefactorQ raw ∧
  0 < originalParentDN raw ∧ 0 < originalParentDD raw ∧
  0 < originalParentDenominator raw ∧
  (originalParentNumerator raw : ℚ) / (originalParentDenominator raw : ℚ) =
    parentJensenRationalQ raw ∧
  originalParentJensenFloorQ raw = roundDown 80 (parentJensenRationalQ raw)

instance (raw : FifthWireRow) : Decidable (ParentScalarFacts raw) := by
  unfold ParentScalarFacts
  infer_instance

/-- The producer's exact grid rescaling really cancels from its weight. -/
theorem original_parent_weight_rescaling (raw : FifthWireRow)
    (hh : ∀ k : Fin 5, (raw.lo k : ℚ) + 1 ≠ 0) :
    (4 * (32 * (raw.grid : ℚ)) *
      (∏ k : Fin 5, (32 * ((raw.lo k : ℚ) + 1) - 32 * (raw.lo k : ℚ)))) /
      ((∏ k : Fin 5, 32 * ((raw.lo k : ℚ) + 1)) *
        (32 * ((raw.lo 4 : ℚ) + 1))) = parentPrefactorQ raw := by
  simp [parentPrefactorQ, Fin.prod_univ_succ]
  <;> field_simp [hh]
  <;> ring

noncomputable section
open P5OldFifthPointwiseQ

/-- Original raw fields to a real Q lower bound, with no fake old floor
licence.  The actual parent vertex-mean/integral step is still separate. -/
theorem original_raw_parent_floor_le_Q (raw : FifthWireRow)
    (hf : ParentScalarFacts raw) :
    (originalParentJensenFloorQ raw : ℝ) ≤
      (parentPrefactorQ raw : ℝ) * Q (parentBQ raw : ℝ) (parentEQ raw : ℝ) := by
  obtain ⟨_hB, _hd, hb, _hb4, he0, he, hp, _hn, _hdd, _hden, _hwire, hfloor⟩ := hf
  rw [hfloor]
  exact original_parent_scalar_floor_sound _ _ _ hp hb he0 he

/-- Original unrounded rational minus the exact original integer floor.
This is a rounding error, NOT oldBranchDefectQ. -/
theorem original_raw_parent_rounding_error (raw : FifthWireRow)
    (hf : ParentScalarFacts raw) :
    0 ≤ parentJensenRationalQ raw - originalParentJensenFloorQ raw ∧
      parentJensenRationalQ raw - originalParentJensenFloorQ raw < 1 / dyadicScale 80 := by
  obtain ⟨_hB, _hd, _hb, _hb4, _he0, _he, _hp, _hn, _hdd, _hden, _hwire, hfloor⟩ := hf
  rw [hfloor]
  exact roundDown_error 80 (parentJensenRationalQ raw)

end
end ImbalancedChen.P5OriginalParentJensenRawFields
