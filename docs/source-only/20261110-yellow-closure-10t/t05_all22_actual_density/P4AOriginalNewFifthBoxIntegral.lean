import ImbalancedChen.P5OriginalParentJensenIntegral
import ImbalancedChen.P2HistoricLogPointInterpreter

/-! The two original new-fifth grids use the same 32-vertex Jensen
calculus. Their actual producer calls rational_floor with four lower
and five upper odd terms. The grid in both the gap scale and the
reciprocal weight is the original row's grid. -/
namespace ImbalancedChen.P4AOriginalNewFifthBoxIntegral
open scoped BigOperators
open P1OriginalPrefixRowDecodeSoundness
open P1OriginalFifthCorrelatedRawBoxGates
open P5OriginalParentJensenRawFields (parentBQ parentEQ parentPrefactorQ)
open P5NamedFifthPayloadSemantics (sourcePicks gapQ cast_gapQ parentVertexQ)
open P5OldFifthChildGapIntegral (Word wordChoice)
open P5OriginalParentJensenGeometry (parentRatioDeficit cast_parentVertexQ)

def oddSumQ (x : ℚ) (n : ℕ) : ℚ :=
  ∑ j ∈ Finset.range n, x ^ (2*j+1) / ((2*j+1 : ℕ) : ℚ)

def fractionBound (b u : ℚ) : ℚ :=
  let a := b-u
  let z := u/(2*(b-1)-u)
  let y := (a-2)/a
  let low := 2*oddSumQ z 4
  let high := 2*oddSumQ y 5 + 2*y^11/(11*(1-y^2))
  (a*low-u*high)/(a*b)

def vertexSum (raw : FifthWireRow) : ℚ :=
  ∑ w : Word, (32 * (raw.grid : ℚ)) * gapQ raw (parentVertexQ raw (wordChoice w))

/-- All predicates here are finite rational relations on the actual
stored wire row and its independent U40 field. -/
def RowFacts (raw : FifthWireRow) (saved : ℕ) : Prop :=
  0 < raw.grid ∧ (∀ i, (1/400 : ℚ) ≤ raw.lower i ∧ raw.upper i ≤ 19/96) ∧
  (raw.vertexGapSum : ℚ) = vertexSum raw ∧
  (0 ≤ (parentRatioDeficit raw false).lower raw.lower raw.upper ∨
    0 ≤ (parentRatioDeficit raw true).lower raw.lower raw.upper) ∧
  2 < parentBQ raw ∧ parentBQ raw ≤ 4 ∧ 0 ≤ parentEQ raw ∧ parentEQ raw ≤ parentBQ raw - 2 ∧
  (saved : ℚ) / 2^80 ≤ parentPrefactorQ raw * fractionBound (parentBQ raw) (parentEQ raw)

instance (raw : FifthWireRow) (saved : ℕ) : Decidable (RowFacts raw saved) := by
  unfold RowFacts
  infer_instance

noncomputable section
open Set MeasureTheory
open P5OldFifthFrozenUpperSurrogate P5OldFifthFrozenGapConcavity
open P5OldFifthPointwiseQ (Q firstF residual sum5)
open P5OriginalParentBoxJensen (vertex boxVolume prefactor integral_frozenKernel_ge_Jensen)
open P5OriginalParentJensenIntegral (parentLeft parentRight parent_box_eq_original)
open P1OriginalFifthRawBoxSelectorEquivalence
open P1LiteralVariableFifthCompactSupplier
open ImbalancedChen.Certificates.P2HistoricLogPointInterpreter (sharp_odd_log_upper oddSum)

theorem author_fraction_le_Q (b u : ℚ) (hb : 2 < b) (hu : 0 ≤ u) (hub : u ≤ b-2) :
    (fractionBound b u : ℝ) ≤ Q (b : ℝ) (u : ℝ) := by
  let a : ℝ := (b : ℝ) - (u : ℝ)
  let z : ℝ := (u : ℝ) / (2*((b : ℝ)-1)-(u : ℝ))
  let y : ℝ := (a-2)/a
  have hbR : (2 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  have huR : (0 : ℝ) ≤ (u : ℝ) := by exact_mod_cast hu
  have hubR : (u : ℝ) ≤ (b : ℝ)-2 := by exact_mod_cast hub
  have ha : 2 ≤ a := by dsimp [a]; linarith only [hubR]
  have ha0 : 0 < a := by linarith
  have hbm : 0 < (b : ℝ)-1 := by linarith
  have ham : 0 < a-1 := by linarith
  have hd : 0 < 2*((b : ℝ)-1)-(u : ℝ) := by dsimp [a] at ha; linarith
  have hz0 : 0 ≤ z := div_nonneg huR hd.le
  have hz1 : z < 1 := by apply (div_lt_one hd).mpr; dsimp [a] at ha; linarith
  have hy0 : 0 ≤ y := div_nonneg (by linarith) ha0.le
  have hy1 : y < 1 := (div_lt_one ha0).mpr (by linarith)
  have hz : (1+z)/(1-z) = ((b : ℝ)-1)/(a-1) := by
    have hn : 1-z ≠ 0 := by linarith
    dsimp [z,a] at *
    field_simp [hd.ne', ham.ne', hn] <;> ring
  have hy : (1+y)/(1-y) = a-1 := by
    have hn : 1-y ≠ 0 := by linarith
    dsimp [y] at *
    field_simp [ha0.ne', hn] <;> ring
  have hl := Real.sum_range_le_log_div hz0 hz1 4
  have hh := sharp_odd_log_upper hy0 hy1 5
  rw [hz] at hl
  rw [hy] at hh
  have hl' : 2 * oddSum z 4 ≤ Real.log (((b : ℝ)-1)/(a-1)) := by
    unfold oddSum
    push_cast
    push_cast at hl
    linarith only [hl]
  have hh' : Real.log (a-1) ≤ 2 * oddSum y 5 + 2*y^11/(11*(1-y^2)) := by
    simpa using hh
  have hnum := sub_le_sub (mul_le_mul_of_nonneg_left hl' ha0.le)
    (mul_le_mul_of_nonneg_left hh' huR)
  have hq : Q (b : ℝ) (u : ℝ) =
      (a * Real.log (((b : ℝ)-1)/(a-1)) - (u : ℝ)*Real.log (a-1))/(a*(b : ℝ)) := by
    rw [Real.log_div hbm.ne' ham.ne']
    unfold Q firstF
    dsimp [a]
    field_simp [ha0.ne', (show 0 < (b : ℝ) by linarith).ne'] <;> ring
  rw [hq]
  simpa [fractionBound, oddSumQ, oddSum, a, z, y] using
    (div_le_div_of_nonneg_right hnum (mul_pos ha0 (by linarith : 0 < (b : ℝ))).le)

private theorem plane_ratio (raw : FifthWireRow)
    (hr : 0 ≤ (parentRatioDeficit raw false).lower raw.lower raw.upper ∨
      0 ≤ (parentRatioDeficit raw true).lower raw.lower raw.upper)
    (t : Fin 5 → ℝ) (ht : t ∈ rawClosedBox raw) (h5 : 0 < t 4) :
    residual (rawCandidate 0 raw t) t ≤ (parentBQ raw : ℝ) := by
  have one (side : Bool) (h : 0 ≤ (parentRatioDeficit raw side).lower raw.lower raw.upper) :
      residual (rawCandidate 0 raw t) t ≤ (parentBQ raw : ℝ) := by
    have heval := (parentRatioDeficit raw side).lower_le_eval raw.lower raw.upper t
      (fun i => (ht i).1) (fun i => (ht i).2)
    have hlo : (0 : ℝ) ≤ ((parentRatioDeficit raw side).lower raw.lower raw.upper : ℝ) := by exact_mod_cast h
    have hid : (parentRatioDeficit raw side).eval t =
        sum5 t + (parentBQ raw : ℝ) * t 4 - (tentPlane (maskSlots 5 raw.mask.toNat) side).eval t := by
      simp [parentRatioDeficit, Affine5.eval_sub, Affine5.eval_add, indicatorAffine_eval, sum5]
    have hcap : rawCandidate 0 raw t ≤ (tentPlane (maskSlots 5 raw.mask.toNat) side).eval t := by
      rw [tentPlane_eval]
      simp only [rawCandidate, mul_zero, sub_zero, VariableEnvelope.v_eq_min]
      cases side
      · exact min_le_left _ _
      · exact min_le_right _ _
    apply (div_le_iff₀ h5).mpr
    rw [hid] at heval
    linarith
  exact hr.elim (one false) (one true)

/-- Original 32-vertex integral soundness, valid for either actual grid.
The frozen fourth majorant uses the same 15 midpoint choices and W3.
All saved d/A/B and Q80 quantities stay attached to their own row. -/
theorem saved_floor_le_box_integral (raw : FifthWireRow) (saved : ℕ) (hf : RowFacts raw saved) :
    (saved : ℝ)/2^80 ≤ ∫ t in raw.originalBox, frozenUpperPositiveKernel (sourcePicks raw) raw t := by
  obtain ⟨hg, hcoord, hd, hratio, hb, hb4, hu, hub, hfloor⟩ := hf
  have hgR : (0 : ℝ) < (raw.grid : ℝ) := by exact_mod_cast hg
  have hleft (i : Fin 5) : 0 < parentLeft raw i := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : (0 : ℚ) < 1/400) (hcoord i).1)
  have hspan (i : Fin 5) : parentLeft raw i < parentRight raw i := by
    simp only [parentLeft, parentRight, FifthWireRow.lower, FifthWireRow.upper]
    push_cast
    exact div_lt_div_of_pos_right (lt_add_one _) hgR
  have hrawlo (i : Fin 5) : (0 : ℝ) < (raw.lo i : ℝ) := by
    have h := hleft i
    simp only [parentLeft, FifthWireRow.lower, Rat.cast_div, Rat.cast_intCast] at h
    by_contra! hn
    exact (not_lt_of_ge (div_nonpos_of_nonpos_of_nonneg hn hgR.le)) h
  have hden (i : Fin 5) : (raw.lo i : ℝ)+1 ≠ 0 := by linarith [hrawlo i]
  have hbox : boxVolume (parentLeft raw) (parentRight raw) * prefactor (parentRight raw) =
      (parentPrefactorQ raw : ℝ) := by
    simp only [boxVolume, prefactor, parentLeft, parentRight, parentPrefactorQ,
      FifthWireRow.lower, FifthWireRow.upper, Fin.prod_univ_succ]
    push_cast
    field_simp [hgR.ne', hden 0, hden 1, hden 2, hden 3, hden 4] <;> ring
  have hgap : (raw.vertexGapSum : ℝ) = (32 * (raw.grid : ℝ)) *
      (∑ w : Word, frozenGap (sourcePicks raw) raw
        (vertex (parentLeft raw) (parentRight raw) (wordChoice w))) := by
    rw [Finset.mul_sum]
    have hz := congrArg (fun q : ℚ => (q : ℝ)) hd
    simpa [vertexSum, cast_gapQ, cast_parentVertexQ, vertex, parentLeft, parentRight,
      P5OriginalParentJensenGeometry.parentVertex] using hz
  have heq : (parentEQ raw : ℝ) = (∑ w : Word, frozenGap (sourcePicks raw) raw
      (vertex (parentLeft raw) (parentRight raw) (wordChoice w))) / 32 / parentRight raw 4 := by
    simp only [parentEQ, parentRight, FifthWireRow.upper]
    push_cast
    rw [hgap]
    field_simp [hgR.ne', hden 4] <;> ring
  have hrealU : (parentEQ raw : ℝ) ∈ Icc 0 ((parentBQ raw : ℝ)-2) := by
    constructor
    · exact_mod_cast hu
    · exact_mod_cast hub
  have hj := integral_frozenKernel_ge_Jensen (sourcePicks raw) raw (parentLeft raw) (parentRight raw)
    hspan hleft (by exact_mod_cast hb) (by exact_mod_cast hb4)
    (fun t ht => plane_ratio raw hratio t (fun i => ⟨ht.1 i, ht.2 i⟩) ((hleft 4).trans_le (ht.1 4)))
    (parentEQ raw : ℝ) hrealU heq
  rw [parent_box_eq_original, hbox] at hj
  have hpr : (0 : ℝ) ≤ (parentPrefactorQ raw : ℝ) := by
    simp only [parentPrefactorQ]
    push_cast
    exact div_nonneg (by positivity) (mul_nonneg (Finset.prod_nonneg (fun i _ => by linarith [hrawlo i]))
      (by linarith [hrawlo 4]))
  have hfloorR : (saved : ℝ) / 2^80 ≤
      (parentPrefactorQ raw : ℝ) * (fractionBound (parentBQ raw) (parentEQ raw) : ℝ) := by
    exact_mod_cast hfloor
  exact hfloorR.trans ((mul_le_mul_of_nonneg_left (author_fraction_le_Q _ _ hb hu hub) hpr).trans hj)

/-- Remove the row's auxiliary frozen fourth majorant.  This is the
actual manuscript raw fifth candidate compared to its raw-15 bound.
The integral uses the literal variable own-cube profiles. -/
theorem saved_floor_le_literal_integral (raw : FifthWireRow) (saved : ℕ) (hf : RowFacts raw saved) :
    (saved : ℝ)/2^80 ≤ ∫ t in raw.originalBox,
      P1OriginalFifthActualB13IntegralError.positiveKernel raw 0 t := by
  have hl (k : Fin 5) : 0 < parentLeft raw k := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : (0 : ℚ) < 1/400) ((hf.2.1 k).1))
  have hF : IntegrableOn (frozenUpperPositiveKernel (sourcePicks raw) raw) raw.originalBox := by
    rw [← parent_box_eq_original]
    exact P5OriginalParentBoxJensen.integrableOn_frozenKernel _ _ _ _ hl
  have hP := P1OriginalFifthActualB13IntegralError.positiveKernel_integrableOn_of_subset raw 0
    raw.originalBox (by
      intro t ht k _
      exact ⟨(show (1/400 : ℝ) ≤ (raw.lower k : ℝ) by exact_mod_cast (hf.2.1 k).1).trans (ht k).1,
        (ht k).2.le.trans (by exact_mod_cast (hf.2.1 k).2)⟩)
  exact (saved_floor_le_box_integral raw saved hf).trans
    (setIntegral_mono_on hF hP (P1FifthGrid400UnitBoxPartition.measurableSet_originalBox raw)
      (fun t ht => frozenUpperPositiveKernel_le_literalPositiveRawKernel (sourcePicks raw) raw t
        (fun k => (hl k).trans_le (ht k).1)))

end
end ImbalancedChen.P4AOriginalNewFifthBoxIntegral
