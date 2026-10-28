import ImbalancedChen.P1FifthNamedParentsConcreteJ5
import ImbalancedChen.P1OriginalFifthRawBoxGateSoundness
import ImbalancedChen.P1FifthUnitBoxGainDecomposition

/-!
SOURCE_ONLY / UNCOMPILED_ZERO_CREDIT.

The two literal saved parents now supply their own complete fifth candidate
checks, not merely the independent third-owner history checks. Their raw
1/400 boxes have different geometry keys. Consequently the existing actual
variable-fifth integral theorem applies to this concrete two-parent family
without an assumed key checker, an assumed selected-owner table membership,
or an assumed fifth gate Boolean.

The finite table is the explicitly chosen local namedJ5. No equality with
the historical full adopted J5, archived byte loader, numerical gain, or K
is asserted. The actual fourth producer profile remains the same variable
parent in both old and new strict-own-cube terms.
-/

namespace ImbalancedChen.P1FifthNamedParentActualIntegral

open P1OriginalPrefixRowDecodeSoundness
open P1OriginalVariableFifthContinuation
open P1OriginalCoarseFifthContinuation
open P1FifthMask6NamedParent0Owner P1FifthMask5NamedParent1Owner
open P1FifthNamedParentsConcreteJ5
open P1OriginalFifthRawBoxGateSoundness

/-- The complete full/selected-square raw check is monotone in its loss.
This is distinct from each named parent's original third-history check. -/
theorem rawBoxGateCheck_of_loss_le (e E : ℚ) (raw : FifthWireRow)
    (he : e ≤ E) (hc : rawBoxGateCheck E raw = true) :
    rawBoxGateCheck e raw = true := by
  have hh := rawBoxGateCheck_sound E raw hc
  apply decide_eq_true
  exact ⟨hh.1, hh.2.1, by linarith [hh.2.2]⟩

/-- Small literal rational checks. No saved-row statistics are used. -/
theorem parent0_complete_raw_gate :
    rawBoxGateCheck (3 / 51200) selectedParent0 = true := by
  decide

theorem parent1_complete_raw_gate :
    rawBoxGateCheck (3 / 51200) selectedParent1 = true := by
  decide

theorem parent0_all_decoded_gates (e : ℚ) (he : e ≤ 3 / 51200)
    (m : ℕ) (r : FifthRow m) (hr : r ∈ decodeFifthRows selectedParent0 m) :
    gateCheck e m r = true :=
  decoded_gateCheck_of_rawBoxGateCheck e selectedParent0 m r hr
    (rawBoxGateCheck_of_loss_le e (3 / 51200) selectedParent0 he
      parent0_complete_raw_gate)

theorem parent1_all_decoded_gates (e : ℚ) (he : e ≤ 3 / 51200)
    (m : ℕ) (r : FifthRow m) (hr : r ∈ decodeFifthRows selectedParent1 m) :
    gateCheck e m r = true :=
  decoded_gateCheck_of_rawBoxGateCheck e selectedParent1 m r hr
    (rawBoxGateCheck_of_loss_le e (3 / 51200) selectedParent1 he
      parent1_complete_raw_gate)

noncomputable section
open Set MeasureTheory
open scoped Classical BigOperators
open P1FifthGrid400UnitBoxPartition P1FifthUnitBoxGainDecomposition
open P1OriginalFifthGrid400RefinedFullBoxCover
open P1OriginalFifthRawBoxSelectorEquivalence
open P1ActualVariableFifthUntruncatedDomination
open P2OriginalFourthCapProducerInterface

/-- Both independent tests are now discharged for each actual contained
cell: original history/rough selection and complete fifth square gates. -/
theorem parent0_original_eligible
    (e : ℚ) (he : e ≤ 3 / 51200) (chi omega : ℝ)
    (m : ℕ) (hstep : logPrimeMeshStep 0 (19 / 96) m ≤ chi)
    (hw : omega ≤ 1 / 400) (r : FifthRow m)
    (hr : r ∈ decodeFifthRows selectedParent0 m)
    (t : Fin 5 → ℝ) (ht : t ∈ logPrimeMeshCell 0 (19 / 96) m r.cell) :
    eligible e chi m omega (namedJ5 m) r t :=
  ⟨parent0_mem_selected_namedJ5 e he chi omega m hstep hw r hr,
    parent0_all_decoded_gates e he m r hr, ht⟩

theorem parent1_original_eligible
    (e : ℚ) (he : e ≤ 3 / 51200) (chi omega : ℝ)
    (m : ℕ) (hstep : logPrimeMeshStep 0 (19 / 96) m ≤ chi)
    (hw : omega ≤ 1 / 400) (r : FifthRow m)
    (hr : r ∈ decodeFifthRows selectedParent1 m)
    (t : Fin 5 → ℝ) (ht : t ∈ logPrimeMeshCell 0 (19 / 96) m r.cell) :
    eligible e chi m omega (namedJ5 m) r t :=
  ⟨parent1_mem_selected_namedJ5 e he chi omega m hstep hw r hr,
    parent1_all_decoded_gates e he m r hr, ht⟩

/-- This equality concerns the explicit local table, not an unspecified
historical adopted J5. Every one of its cells passes the original filter. -/
theorem selected_namedJ5_eq
    (e : ℚ) (he : e ≤ 3 / 51200) (chi omega : ℝ)
    (m : ℕ) (hstep : logPrimeMeshStep 0 (19 / 96) m ≤ chi)
    (hw : omega ≤ 1 / 400) :
    selectedFifthCells e chi m omega (namedJ5 m) = namedJ5 m := by
  ext j
  constructor
  · intro hj
    exact ((mem_selectedFifthCells e chi m omega (namedJ5 m) j).mp hj).1
  · intro hj
    change j ∈ ((decodeFifthRows selectedParent0 m).image FifthRow.cell) ∪
      ((decodeFifthRows selectedParent1 m).image FifthRow.cell) at hj
    rcases Finset.mem_union.mp hj with h0 | h1
    · obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp h0
      exact parent0_mem_selected_namedJ5 e he chi omega m hstep hw r hr
    · obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp h1
      exact parent1_mem_selected_namedJ5 e he chi omega m hstep hw r hr

/-- Literal source rows only. Their saved A/B/gap fields are not cap data. -/
def namedRecords : Finset FifthWireRow := {selectedParent0, selectedParent1}

theorem parent_keys_ne : rowKey selectedParent0 ≠ rowKey selectedParent1 := by
  intro h
  have hh := congrFun h (0 : Fin 5)
  norm_num [rowKey, selectedParent0, selectedParent1] at hh

theorem parents_ne : selectedParent0 ≠ selectedParent1 := by
  intro h
  exact parent_keys_ne (congrArg rowKey h)

theorem named_grid : ∀ raw ∈ namedRecords, raw.grid = 400 := by
  intro raw hr
  simp only [namedRecords, Finset.mem_insert, Finset.mem_singleton] at hr
  rcases hr with rfl | rfl <;> rfl

theorem named_mask : ∀ raw ∈ namedRecords, 0 ≤ raw.mask := by
  intro raw hr
  simp only [namedRecords, Finset.mem_insert, Finset.mem_singleton] at hr
  rcases hr with rfl | rfl <;> norm_num [selectedParent0, selectedParent1]

/-- Unlike Finset deduplication, distinct geometry keys license true raw
box disjointness even if the metadata fields were to change. -/
theorem named_keys_injective : KeyInjective namedRecords := by
  intro a ha b hb hab
  simp only [namedRecords, Finset.mem_insert, Finset.mem_singleton] at ha hb
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · rfl
  · exact (parent_keys_ne hab).elim
  · exact (parent_keys_ne hab.symm).elim
  · rfl

theorem named_raw_boxes_disjoint :
    Disjoint selectedParent0.originalBox selectedParent1.originalBox :=
  unit_boxes_disjoint_of_key_ne selectedParent0 selectedParent1 rfl rfl parent_keys_ne

/-- The exact actually-used refined family has no unproved Boolean gate
hypothesis. The proof never enumerates its (potentially huge) cell set. -/
theorem named_family_gates (e : ℚ) (he : e ≤ 3 / 51200) (q : ℕ) :
    ∀ r ∈ decodedFamily namedRecords q,
      gateCheck e (refinedMesh q) r = true := by
  apply decodedFamily_gates_of_raw_checks namedRecords q e
  intro raw hr
  simp only [namedRecords, Finset.mem_insert, Finset.mem_singleton] at hr
  rcases hr with rfl | rfl
  · exact rawBoxGateCheck_of_loss_le e (3 / 51200) selectedParent0 he
      parent0_complete_raw_gate
  · exact rawBoxGateCheck_of_loss_le e (3 / 51200) selectedParent1 he
      parent1_complete_raw_gate

/-- Exact same-parent full integral split for the concrete selected family.
Both old and new strict fifth-own-cube terms and the variable fourth
producer profile are the original actual ones. No numerical lower bound,
constant inherited cap, final upper estimate, or adopted-table identity is
among the assumptions. This is a local finite-tree identity. -/
theorem actual_selected_integral_eq_two_named_parents
    (q : ℕ) (hq : 0 < q) (e : ℚ) (he : 0 ≤ e) (hemax : e ≤ 3 / 51200)
    (chi omega : ℝ)
    (hstep : logPrimeMeshStep 0 (19 / 96) (refinedMesh q) ≤ chi)
    (homega : 0 < omega) (hw : omega ≤ 1 / 400)
    (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop) :
    fullSelectedIntegral e chi (refinedMesh q) omega rows4 licensed4
        (namedJ5 (refinedMesh q)) (decodedFamily namedRecords q) =
      (∑ j ∈ namedJ5 (refinedMesh q),
        rawOwnerIntegral selectedParent0 e chi (refinedMesh q) omega j rows4 licensed4) +
      (∑ j ∈ namedJ5 (refinedMesh q),
        rawOwnerIntegral selectedParent1 e chi (refinedMesh q) omega j rows4 licensed4) := by
  have homegaRho : omega < (19 / 96 : ℝ) := by linarith
  have hid := fullSelectedIntegral_eq_sum_raw_owner_integrals
    namedRecords q hq named_grid named_mask named_keys_injective
    e chi omega rows4 licensed4 (named_family_gates e hemax q)
    he homega homegaRho (namedJ5 (refinedMesh q))
  rw [selected_namedJ5_eq e hemax chi omega (refinedMesh q) hstep hw] at hid
  simpa [namedRecords, parents_ne] using hid

end
end ImbalancedChen.P1FifthNamedParentActualIntegral
