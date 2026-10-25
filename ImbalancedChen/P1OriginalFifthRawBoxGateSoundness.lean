import ImbalancedChen.P1OriginalFifthRawBoxSelectorEquivalence

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.
A pure rational sufficient gate test per original saved fifth box implies
the actual variable-candidate gateCheck on EVERY contained decoded cell.
The proof uses endpoint monotonicity, never enumerates refined cells, and
does not replace M_I(t) by a stored constant cap. The raw-box condition may
be stronger than a historical acceptance test; no saved row is claimed to
pass it. Original owner licences, parents, and history are separate inputs.
-/

namespace ImbalancedChen.P1OriginalFifthRawBoxGateSoundness
open scoped BigOperators
open VariableEnvelope
open P1OriginalPrefixRowDecodeSoundness

/-- Computable rational raw-box test, including the signed wire guards.
This definition precedes Classical: no real or classical decision is used. -/
def rawBoxGateCheck (e : ℚ) (raw : FifthWireRow) : Bool :=
  decide (0 < raw.grid ∧ 0 ≤ raw.mask ∧
    selectedCapLower (maskSlots 5 raw.mask.toNat) 0 raw.upper + 2 * e <
      qVLo (∑ i ∈ maskSlots 5 raw.mask.toNat, raw.lower i)
        (∑ i ∈ maskSlots 5 raw.mask.toNat, raw.upper i))

/-- One finite check per raw record; no expansion into refined mesh cells. -/
def rawFamilyGateCheck (e : ℚ) (records : Finset FifthWireRow) : Bool :=
  @decide _ (Finset.decidableDforallFinset (s := records)
    (p := fun raw _ => rawBoxGateCheck e raw = true))

noncomputable section
open Set
open scoped Classical
open P1OriginalVariableFifthContinuation
open P1OriginalFifthGrid400RefinedFullBoxCover
open P1OriginalFifthRawBoxSelectorEquivalence
open P2OriginalFourthCapProducerInterface
open P1CorrectedFifthDensityDictionary
open P1CorrectedFifthCausalTupleDictionary

theorem prefixSquareExpr_mono_rat {n : ℕ} {u v : Fin n → ℚ}
    (h : ∀ i, u i ≤ v i) (j : Fin n) :
    prefixSquareExpr u j ≤ prefixSquareExpr v j := by
  unfold prefixSquareExpr
  exact add_le_add (Finset.sum_le_sum (fun i _ => h i))
    (mul_le_mul_of_nonneg_left (h j) (by norm_num))

theorem selectedSquareExpr_mono_rat {n : ℕ} (I : Finset (Fin n))
    {u v : Fin n → ℚ} (h : ∀ i, u i ≤ v i) (j : Fin n) :
    selectedSquareExpr I u j ≤ selectedSquareExpr I v j := by
  unfold selectedSquareExpr
  exact add_le_add
    (add_le_add (Finset.sum_le_sum (fun i _ => h i))
      (Finset.sum_le_sum (fun i _ => h i)))
    (mul_le_mul_of_nonneg_left (h j) (by norm_num))

/-- Every square-gate upper bound decreases under coordinate refinement. -/
theorem selectedCapLower_mono_rat {n : ℕ} (I : Finset (Fin n)) (old : ℚ)
    {u v : Fin n → ℚ} (h : ∀ i, u i ≤ v i) :
    selectedCapLower I old u ≤ selectedCapLower I old v := by
  apply Finset.max'_le
  intro value hv
  simp only [selectedCapLowerSet, Finset.mem_insert, Finset.mem_union,
    Finset.mem_image] at hv
  rcases hv with rfl | rfl | ⟨j, _hj, rfl⟩ | ⟨j, hj, rfl⟩
  · exact selectedCapLower_old_le I old v
  · exact selectedCapLower_half_le I old v
  · exact (prefixSquareExpr_mono_rat h j).trans (selectedCapLower_prefix_le I old v j)
  · exact (selectedSquareExpr_mono_rat I h j).trans
      (selectedCapLower_selected_le I old v j (Finset.mem_sdiff.mp hj).2)

/-- The rational tent lower bound increases when its interval narrows;
this remains true for intervals crossing the tent's peak. -/
theorem qVLo_mono_narrower {l u l' u' : ℚ} (hl : l ≤ l') (hu : u' ≤ u) :
    qVLo l u ≤ qVLo l' u' := by
  unfold qVLo
  apply min_le_min
  · dsimp [qA]
    linarith
  · dsimp [qC]
    linarith

theorem rawBoxGateCheck_sound (e : ℚ) (raw : FifthWireRow)
    (hc : rawBoxGateCheck e raw = true) :
    0 < raw.grid ∧ 0 ≤ raw.mask ∧
      selectedCapLower (maskSlots 5 raw.mask.toNat) 0 raw.upper + 2 * e <
        qVLo (∑ i ∈ maskSlots 5 raw.mask.toNat, raw.lower i)
          (∑ i ∈ maskSlots 5 raw.mask.toNat, raw.upper i) := by
  exact of_decide_eq_true hc

/-- One raw-box check proves the actual gate for an arbitrary contained
decoded subcell, on any mesh; no grid400 or expansion assumption is needed. -/
theorem decoded_gateCheck_of_rawBoxGateCheck (e : ℚ) (raw : FifthWireRow)
    (m : ℕ) (r : FifthRow m) (hr : r ∈ decodeFifthRows raw m)
    (hc : rawBoxGateCheck e raw = true) : gateCheck e m r = true := by
  have hraw := (rawBoxGateCheck_sound e raw hc).2.2
  obtain ⟨_hg, _hm, j, hj, rfl⟩ := (mem_decodeFifthRows_iff raw m r).mp hr
  have hupper := selectedCapLower_mono_rat (maskSlots 5 raw.mask.toNat) 0
    (fun i => (hj i).2)
  have hsumlo : (∑ i ∈ maskSlots 5 raw.mask.toNat, raw.lower i) ≤
      ∑ i ∈ maskSlots 5 raw.mask.toNat, qLogPrimeMeshLo 0 (19 / 96) m j i :=
    Finset.sum_le_sum (fun i _ => (hj i).1)
  have hsumhi : (∑ i ∈ maskSlots 5 raw.mask.toNat, qLogPrimeMeshHi 0 (19 / 96) m j i) ≤
      ∑ i ∈ maskSlots 5 raw.mask.toNat, raw.upper i :=
    Finset.sum_le_sum (fun i _ => (hj i).2)
  have htent := qVLo_mono_narrower hsumlo hsumhi
  have hgate : selectedCapLower (maskSlots 5 raw.mask.toNat) 0
        (qLogPrimeMeshHi 0 (19 / 96) m j) + 2 * e <
      qVLo (∑ i ∈ maskSlots 5 raw.mask.toNat, qLogPrimeMeshLo 0 (19 / 96) m j i)
        (∑ i ∈ maskSlots 5 raw.mask.toNat, qLogPrimeMeshHi 0 (19 / 96) m j i) :=
    (add_le_add_right hupper (2 * e)).trans_lt (hraw.trans_le htent)
  exact decide_eq_true hgate

theorem decodedFamily_gates_of_raw_checks (records : Finset FifthWireRow)
    (q : ℕ) (e : ℚ) (hcheck : ∀ raw ∈ records, rawBoxGateCheck e raw = true) :
    ∀ r ∈ decodedFamily records q, gateCheck e (refinedMesh q) r = true := by
  intro r hr
  obtain ⟨raw, hraw, hdecode⟩ := (mem_decodedFamily records q r).mp hr
  exact decoded_gateCheck_of_rawBoxGateCheck e raw (refinedMesh q) r hdecode (hcheck raw hraw)

theorem rawFamilyGateCheck_sound (records : Finset FifthWireRow) (e : ℚ)
    (hc : rawFamilyGateCheck e records = true) :
    ∀ raw ∈ records, rawBoxGateCheck e raw = true := by
  exact of_decide_eq_true hc

theorem decodedFamily_gates_of_rawFamilyGateCheck (records : Finset FifthWireRow)
    (q : ℕ) (e : ℚ) (hc : rawFamilyGateCheck e records = true) :
    ∀ r ∈ decodedFamily records q, gateCheck e (refinedMesh q) r = true :=
  decodedFamily_gates_of_raw_checks records q e (rawFamilyGateCheck_sound records e hc)

/-- The finite raw-box check replaces the potentially enormous per-cell
gate premise in the exact actual variable-fifth maximum connection. -/
theorem checked_rawBoxMaximum_eq_actualNext5
    (records : Finset FifthWireRow) (q : ℕ) (hq : 0 < q)
    (hgrid : ∀ raw ∈ records, raw.grid = 400)
    (e : ℚ) (hc : rawFamilyGateCheck e records = true)
    (chi omega : ℝ) (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
    (j : RefinedCell q) (t : Fin 5 → ℝ)
    (ht : t ∈ logPrimeMeshCell 0 (19 / 96) (refinedMesh q) j) :
    rawBoxMaximum (e : ℝ) records
        (originalVariableFourthProfile e chi omega (refinedMesh q) j rows4 licensed4 t) t =
      P1ActualVariableFifthProfiles.actualNext5 e chi (refinedMesh q) omega j
        rows4 licensed4 (decodedFamily records q) t := by
  have hchecks := rawFamilyGateCheck_sound records e hc
  exact rawBoxMaximum_eq_actualNext5 records q hq hgrid
    (fun raw hraw => (rawBoxGateCheck_sound e raw (hchecks raw hraw)).2.1)
    e chi omega rows4 licensed4 j t ht
    (decodedFamily_gates_of_raw_checks records q e hchecks)

/-- Original selected-owner licensing and its inherited fourth seed are
still required separately; the raw checker fabricates neither one. -/
theorem checked_rawBoxMaximum_eq_original_exponent5
    (records : Finset FifthWireRow) (q : ℕ) (hq : 0 < q)
    (hgrid : ∀ raw ∈ records, raw.grid = 400)
    (e : ℚ) (hc : rawFamilyGateCheck e records = true)
    (chi omega : ℝ) (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
    (J5 : Finset (RefinedCell q)) (N : ℕ) (hN : 1 < N)
    (p : Fin 5 → ℕ) (hp : ∀ i, 0 < p i) (j : RefinedCell q)
    (hj : j ∈ P1OriginalCoarseFifthContinuation.selectedFifthCells e chi (refinedMesh q) omega J5)
    (ht : actualPrimeTupleLog N p ∈ logPrimeMeshCell 0 (19 / 96) (refinedMesh q) j) :
    rawBoxMaximum (e : ℝ) records
        (originalVariableFourthProfile e chi omega (refinedMesh q) j rows4 licensed4
          (actualPrimeTupleLog N p)) (actualPrimeTupleLog N p) =
      exponent5 e chi (refinedMesh q) omega (N : ℝ) rows4 licensed4 J5
        (decodedFamily records q) (tupleHistory p) := by
  have hchecks := rawFamilyGateCheck_sound records e hc
  exact rawBoxMaximum_eq_original_exponent5 records q hq hgrid
    (fun raw hraw => (rawBoxGateCheck_sound e raw (hchecks raw hraw)).2.1)
    e chi omega rows4 licensed4 J5 N hN p hp j hj ht
    (decodedFamily_gates_of_raw_checks records q e hchecks)

end
end ImbalancedChen.P1OriginalFifthRawBoxGateSoundness
