import ImbalancedChen.P1OriginalFourthIntegerCubeGateSemantics

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED / ZERO_CREDIT.

Generic mathematical-integer residual and complete per-row admission
semantics for certify_fourth_prefix_stronger.py, SHA256
25069573985d30beae59a1a2a89ddeb79e56f696e78a5fae5153de0bb8bd378a.
The source upper=-lower(-a), R0=max_old min_line upper(old-SUM), and
R1=max(R0,min_new upper(new-SUM)) are retained literally. No independent
interval subtraction replaces a shared-affine difference.

The finite Boolean below is a symbolic specification: no record is run
through it. Host int64 overflow, parsing the whole payload, family dyadic
disjointness and all saved analytic certificate statistics remain separate.
-/

namespace ImbalancedChen.P1OriginalFourthIntegerGeometryAdmission
open P2OriginalFourthCapProducerInterface
open P1OriginalPrefixRowDecodeSoundness
open P1OriginalPrefixRowFiniteCheckSoundness
open P1OriginalFourthIntegerGapSemantics
open P1OriginalFourthIntegerCubeGateSemantics
open scoped BigOperators

noncomputable section

def integerNeg (a : IntegerAffine) : IntegerAffine :=
  ⟨-a.constant, fun i => -a.coefficient i⟩

def integerUpper (a : IntegerAffine) (lo hi : Fin 4 → ℕ) : ℤ :=
  -(integerNeg a).lower lo hi

def sourceSum : IntegerAffine := ⟨0, fun _ => 32⟩

def commonOldResidualPiece (raw : FourthWireRow) (j : Fin 6) : ℤ :=
  min (integerUpper ((sourceOld j false).sub sourceSum) raw.lo raw.hi)
    (integerUpper ((sourceOld j true).sub sourceSum) raw.lo raw.hi)

/-- Source-order old residual piece, including the original singleton B. -/
def programOldResidualPiece (raw : FourthWireRow) (j : Fin 6) : ℤ :=
  commonOldResidualPiece raw (pythonToCommon j)

def integerR0 (raw : FourthWireRow) : ℤ :=
  Finset.univ.sup' (show (Finset.univ : Finset (Fin 6)).Nonempty from ⟨0, by simp⟩)
    (programOldResidualPiece raw)

def integerNewResidualPiece (raw : FourthWireRow) : ℤ :=
  min (integerUpper ((sourceTent raw.toProducerRow.selected false).sub sourceSum) raw.lo raw.hi)
    (integerUpper ((sourceTent raw.toProducerRow.selected true).sub sourceSum) raw.lo raw.hi)

def integerR1 (raw : FourthWireRow) : ℤ :=
  max (integerR0 raw) (integerNewResidualPiece raw)

def integerResidualRows (raw : FourthWireRow) : Prop :=
  0 < integerR0 raw ∧ integerR1 raw < 160 * (raw.lo 3 : ℤ)

/-- Complete mathematical-integer PER-ROW geometry admission. This does
not include family disjointness, derivative tables, integrals or gains. -/
def integerGeometryRows (raw : FourthWireRow) : Prop :=
  integerDomainRows raw ∧ 0 < integerDelta raw ∧ 0 < integerOldCubeSlack raw ∧
    integerGateRows raw ∧ integerResidualRows raw

/-- A finite integer comparison specification, never evaluated here.
The explicit finite decidability is constructed without Classical. -/
def integerGeometryAccept (raw : FourthWireRow) : Bool :=
  @decide (integerGeometryRows raw) (by
    unfold integerGeometryRows integerDomainRows integerGateRows integerResidualRows
    infer_instance)

open scoped Classical

theorem toAffine_integerNeg (a : IntegerAffine) :
    (integerNeg a).toAffine = a.toAffine.neg := by
  apply congrArg₂ Affine.mk
  · simp only [integerNeg, IntegerAffine.toAffine, Affine.neg, Int.cast_neg]
    ring
  · funext i
    simp only [integerNeg, IntegerAffine.toAffine, Affine.neg, Int.cast_neg]
    ring

theorem sourceSum_toAffine : sourceSum.toAffine = sumAffine := by
  apply congrArg₂ Affine.mk
  · norm_num [sourceSum, IntegerAffine.toAffine, sumAffine]
  · funext i
    norm_num [sourceSum, IntegerAffine.toAffine, sumAffine]

theorem upper_scaled (a : IntegerAffine) (lo hi : Fin 4 → ℕ) :
    a.toAffine.upper (endpoint lo) (endpoint hi) = (integerUpper a lo hi : ℚ) / 6553600 := by
  calc
    a.toAffine.upper (endpoint lo) (endpoint hi) =
        -((integerNeg a).toAffine.lower (endpoint lo) (endpoint hi)) := by
      simpa only [toAffine_integerNeg, Affine.upper]
    _ = -( (integerNeg a).lower lo hi : ℚ) / 6553600 := by
      rw [lower_scaled]
      ring
    _ = (integerUpper a lo hi : ℚ) / 6553600 := by
      simp only [integerUpper, Int.cast_neg]

theorem upper_positive_iff (a : IntegerAffine) (lo hi : Fin 4 → ℕ) :
    (0 : ℚ) < a.toAffine.upper (endpoint lo) (endpoint hi) ↔ 0 < integerUpper a lo hi := by
  rw [upper_scaled]
  constructor
  · intro h
    have : (0 : ℚ) < (integerUpper a lo hi : ℚ) := by linarith
    exact_mod_cast this
  · intro h
    have : (0 : ℚ) < (integerUpper a lo hi : ℚ) := by exact_mod_cast h
    positivity

/-- 5*t_last has integer numerator160*lo_last because D/N=32. -/
theorem upper_lt_five_last_iff (a : IntegerAffine) (lo hi : Fin 4 → ℕ) :
    a.toAffine.upper (endpoint lo) (endpoint hi) < 5 * endpoint lo 3 ↔
      integerUpper a lo hi < 160 * (lo 3 : ℤ) := by
  rw [upper_scaled]
  change (integerUpper a lo hi : ℚ) / 6553600 < 5 * ((lo 3 : ℚ) / 204800) ↔ _
  constructor
  · intro h
    have : (integerUpper a lo hi : ℚ) < 160 * (lo 3 : ℚ) := by linarith
    exact_mod_cast this
  · intro h
    have : (integerUpper a lo hi : ℚ) < 160 * (lo 3 : ℚ) := by exact_mod_cast h
    linarith

theorem old_residual_positive_iff (raw : FourthWireRow) (j : Fin 6) :
    (0 : ℚ) < min
      (((oldPiece j false).sub sumAffine).upper raw.toProducerRow.lower raw.toProducerRow.upper)
      (((oldPiece j true).sub sumAffine).upper raw.toProducerRow.lower raw.toProducerRow.upper) ↔
    0 < commonOldResidualPiece raw j := by
  have h0 := upper_positive_iff ((sourceOld j false).sub sourceSum) raw.lo raw.hi
  have h1 := upper_positive_iff ((sourceOld j true).sub sourceSum) raw.lo raw.hi
  simp only [toAffine_sub, sourceOld_toAffine, sourceSum_toAffine] at h0 h1
  simp only [commonOldResidualPiece, lt_min_iff]
  exact and_congr h0 h1

theorem old_residual_upper_iff (raw : FourthWireRow) (j : Fin 6) :
    min (((oldPiece j false).sub sumAffine).upper raw.toProducerRow.lower raw.toProducerRow.upper)
      (((oldPiece j true).sub sumAffine).upper raw.toProducerRow.lower raw.toProducerRow.upper) <
        5 * raw.toProducerRow.lower 3 ↔
    commonOldResidualPiece raw j < 160 * (raw.lo 3 : ℤ) := by
  have h0 := upper_lt_five_last_iff ((sourceOld j false).sub sourceSum) raw.lo raw.hi
  have h1 := upper_lt_five_last_iff ((sourceOld j true).sub sourceSum) raw.lo raw.hi
  simp only [toAffine_sub, sourceOld_toAffine, sourceSum_toAffine] at h0 h1
  simp only [commonOldResidualPiece, min_lt_iff]
  exact or_congr h0 h1

theorem new_residual_upper_iff (raw : FourthWireRow) :
    min (((tentPlane raw.toProducerRow.selected false).sub sumAffine).upper
      raw.toProducerRow.lower raw.toProducerRow.upper)
      (((tentPlane raw.toProducerRow.selected true).sub sumAffine).upper
        raw.toProducerRow.lower raw.toProducerRow.upper) < 5 * raw.toProducerRow.lower 3 ↔
      integerNewResidualPiece raw < 160 * (raw.lo 3 : ℤ) := by
  have h0 := upper_lt_five_last_iff
    ((sourceTent raw.toProducerRow.selected false).sub sourceSum) raw.lo raw.hi
  have h1 := upper_lt_five_last_iff
    ((sourceTent raw.toProducerRow.selected true).sub sourceSum) raw.lo raw.hi
  simp only [toAffine_sub, sourceTent_toAffine, sourceSum_toAffine] at h0 h1
  simp only [integerNewResidualPiece, min_lt_iff]
  exact or_congr h0 h1

def rationalResidualRows (raw : FourthWireRow) : Prop :=
  (∃ j : Fin 6, (0 : ℚ) <
    min (((oldPiece j false).sub sumAffine).upper raw.toProducerRow.lower raw.toProducerRow.upper)
      (((oldPiece j true).sub sumAffine).upper raw.toProducerRow.lower raw.toProducerRow.upper)) ∧
  (∀ j : Fin 6,
    min (((oldPiece j false).sub sumAffine).upper raw.toProducerRow.lower raw.toProducerRow.upper)
      (((oldPiece j true).sub sumAffine).upper raw.toProducerRow.lower raw.toProducerRow.upper) <
        5 * raw.toProducerRow.lower 3) ∧
  min (((tentPlane raw.toProducerRow.selected false).sub sumAffine).upper
      raw.toProducerRow.lower raw.toProducerRow.upper)
    (((tentPlane raw.toProducerRow.selected true).sub sumAffine).upper
      raw.toProducerRow.lower raw.toProducerRow.upper) < 5 * raw.toProducerRow.lower 3

/-- Original max-old/min-line residual bounds, with unchanged source order. -/
theorem integerResidualRows_iff (raw : FourthWireRow) :
    integerResidualRows raw ↔ rationalResidualRows raw := by
  constructor
  · rintro ⟨hpositive, hupper⟩
    obtain ⟨j, _hj, hj⟩ := (Finset.lt_sup'_iff _).mp hpositive
    refine ⟨⟨pythonToCommon j, (old_residual_positive_iff raw (pythonToCommon j)).mpr hj⟩, ?_, ?_⟩
    · intro j
      apply (old_residual_upper_iff raw j).mpr
      have hle : programOldResidualPiece raw (commonToPython j) ≤ integerR0 raw :=
        Finset.le_sup' _ (Finset.mem_univ _)
      have ht : programOldResidualPiece raw (commonToPython j) < 160 * (raw.lo 3 : ℤ) :=
        lt_of_le_of_lt (hle.trans (le_max_left _ _)) hupper
      simpa only [programOldResidualPiece, pythonToCommon_commonToPython] using ht
    · apply (new_residual_upper_iff raw).mpr
      exact lt_of_le_of_lt (le_max_right _ _) hupper
  · rintro ⟨⟨j, hj⟩, hold, hnew⟩
    refine ⟨?_, ?_⟩
    · apply (Finset.lt_sup'_iff _).mpr
      refine ⟨commonToPython j, Finset.mem_univ _, ?_⟩
      have h := (old_residual_positive_iff raw j).mp hj
      simpa only [programOldResidualPiece, pythonToCommon_commonToPython] using h
    · apply max_lt
      · apply (Finset.sup'_lt_iff _).mpr
        intro j _hj
        exact (old_residual_upper_iff raw (pythonToCommon j)).mp (hold (pythonToCommon j))
      · exact (new_residual_upper_iff raw).mp hnew

/-- No geometry or checker success premise is smuggled into admission:
all primitive integer comparisons are explicitly expanded above. -/
theorem integerGeometryRows_iff (raw : FourthWireRow) :
    integerGeometryRows raw ↔ fourthGeometryRowsQ raw := by
  constructor
  · rintro ⟨hdomain, hgap, hcube, hgates, hresidual⟩
    rcases (integerDomainRows_iff raw).mp hdomain with ⟨hm0, hm1, hw, ho, hlo, hhi⟩
    have hgapQ := (integerCorrelatedGapRows_iff raw).mp ((integerDelta_pos_iff raw).mp hgap)
    have hcubeQ := (integerCubeRows_iff raw).mp ((integerOldCubeSlack_pos_iff raw).mp hcube)
    have hgatesQ := (integerGateRows_iff raw).mp hgates
    rcases (integerResidualRows_iff raw).mp hresidual with ⟨hr0, hrold, hrnew⟩
    exact ⟨hm0, hm1, hw, ho, hlo, hhi, hgapQ, hcubeQ, hgatesQ, hr0, hrold, hrnew⟩
  · rintro ⟨hm0, hm1, hw, ho, hlo, hhi, hgap, hcube, hgates, hr0, hrold, hrnew⟩
    refine ⟨(integerDomainRows_iff raw).mpr ⟨hm0, hm1, hw, ho, hlo, hhi⟩, ?_, ?_,
      (integerGateRows_iff raw).mpr hgates, (integerResidualRows_iff raw).mpr ⟨hr0, hrold, hrnew⟩⟩
    · exact (integerDelta_pos_iff raw).mpr ((integerCorrelatedGapRows_iff raw).mpr hgap)
    · exact (integerOldCubeSlack_pos_iff raw).mpr ((integerCubeRows_iff raw).mpr hcube)

theorem integerGeometryAccept_iff (raw : FourthWireRow) :
    integerGeometryAccept raw = true ↔ integerGeometryRows raw := by
  simp only [integerGeometryAccept, decide_eq_true_eq]

theorem integerGeometryAccept_check_iff (raw : FourthWireRow) :
    integerGeometryAccept raw = true ↔ fourthGeometryCheck raw = true := by
  rw [integerGeometryAccept_iff, fourthGeometryCheck_iff, integerGeometryRows_iff]

/-- Any symbolic original integer-admitted row passes the existing actual
rational checker. No historical row is asserted to meet this premise. -/
theorem integerGeometryAccept_check (raw : FourthWireRow)
    (h : integerGeometryAccept raw = true) : fourthGeometryCheck raw = true :=
  (integerGeometryAccept_check_iff raw).mp h

theorem integerGeometryAccept_geometry (raw : FourthWireRow)
    (h : integerGeometryAccept raw = true) : raw.toProducerRow.Geometry :=
  fourthGeometryCheck_sound raw (integerGeometryAccept_check raw h)

end
end ImbalancedChen.P1OriginalFourthIntegerGeometryAdmission
