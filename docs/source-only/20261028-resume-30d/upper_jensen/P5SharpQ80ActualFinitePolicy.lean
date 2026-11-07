import ImbalancedChen.P5NamedOwnerReserveArbitraryTolerance
import ImbalancedChen.P5NamedFifthQ80FloorSoundness

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
The original sharp directed-log Q80 expressions, with actual child-specific
b_C, are consumed directly. Their symbolic total is NOT evaluated, and no
historical archived byte equality is asserted. This module supplies the
remaining arbitrary-tolerance actual finite-policy integral connection.
-/
namespace ImbalancedChen.P5SharpQ80ActualFinitePolicy
noncomputable section
open Set MeasureTheory
open scoped Classical BigOperators
open P1OriginalPrefixRowDecodeSoundness
open P1OriginalVariableFifthContinuation
open P1OriginalFifthGrid400RefinedFullBoxCover
open P1FifthMask6NamedParent0Owner P1FifthMask5NamedParent1Owner
open P1FifthNamedParentsConcreteJ5
open P1FifthUnitBoxGainDecomposition
open P1FifthPositivePartActualOwner
open P2OriginalFourthCapProducerInterface
open P5NamedFifthAllChildren
open P5OldFifthExact64ChildTiling
open P5NamedAllChildrenSelectedJensen
open P5NamedOwnerReserveArbitraryTolerance
open P5NamedFifthQ80FloorSoundness

/-- The exact finite128 rational Q80 sum, preserving the source floor
formula. This is a definition, not a claimed computed numerical value. -/
def namedSharpQ80Total : ℚ :=
  ∑ tag : Bool, ∑ c : ChildIndex, childFloorQ tag c

theorem namedSharpQ80Total_nonneg : 0 ≤ namedSharpQ80Total := by
  exact Finset.sum_nonneg (fun tag _ => Finset.sum_nonneg (fun c _ => childFloorQ_nonneg tag c))

/-- Genuine child-specific sharp Q80 floors attain their total minus eta
on ONE actual original named policy, chosen before N. The proof consumes
the real logarithm/floor theorem and the independently constructed actual
zero-omission/common-buffer schedule; neither conclusion is assumed. -/
theorem exists_actual_named_policy_ge_sharpQ80_sub_tolerance
    (eta omega : ℝ) (heta : 0 < eta) (homega : 0 < omega) (hw : omega ≤ 1 / 400)
    (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
    (hgeometry : ∀ r ∈ rows4, licensed4 r → r.Geometry) :
    ∃ e : ℚ, ∃ q : ℕ,
      0 < (e : ℝ) ∧ (e : ℝ) < 3 / 51200 ∧ 0 < q ∧
      (∑ tag : Bool, namedReserveTotal tag e ((e : ℝ) / 20) (refinedMesh q) omega
        (namedJ5 (refinedMesh q))) < eta ∧
      (namedSharpQ80Total : ℝ) - eta ≤
        P1ActualVariableFifthUntruncatedDomination.fullSelectedIntegral e ((e : ℝ) / 20)
          (refinedMesh q) omega rows4 licensed4 (namedJ5 (refinedMesh q))
          (decodedFamily P1FifthNamedParentActualIntegral.namedRecords q) := by
  obtain ⟨e, q, he, hecap, hq, hstep, _, _, hreserve⟩ :=
    exists_named_common_policy_reserve_lt eta omega heta homega hw
  have heQ : 0 ≤ e := by exact_mod_cast he.le
  have hcapQ : e ≤ 3 / 51200 := by exact_mod_cast hecap.le
  have homegaRho : omega < (19 / 96 : ℝ) := by linarith
  have hpositive : ∀ raw ∈ P1FifthNamedParentActualIntegral.namedRecords,
      ∀ i, 1 ≤ raw.lo i := by
    intro raw hr i
    simp only [P1FifthNamedParentActualIntegral.namedRecords,
      Finset.mem_insert, Finset.mem_singleton] at hr
    rcases hr with rfl | rfl
    · exact named_positive_indices false i
    · exact named_positive_indices true i
  have hlocal (tag : Bool) :
      (∑ c : ChildIndex, (childFloorQ tag c : ℝ)) -
          namedReserveTotal tag e ((e : ℝ) / 20) (refinedMesh q) omega (namedJ5 (refinedMesh q)) ≤
        ∑ j ∈ P1OriginalCoarseFifthContinuation.selectedFifthCells
            e ((e : ℝ) / 20) (refinedMesh q) omega (namedJ5 (refinedMesh q)),
          rawOwnerIntegral (namedParent tag) e ((e : ℝ) / 20) (refinedMesh q) omega j
            rows4 licensed4 := by
    have hlit := all64_Q80_floors_minus_reserve_le_original_owner_sum tag e
      ((e : ℝ) / 20) (refinedMesh q) omega (namedJ5 (refinedMesh q))
    apply hlit.trans
    apply Finset.sum_le_sum
    intro j hj
    exact literalPositiveRawOwnerIntegral_le_actual P1FifthNamedParentActualIntegral.namedRecords
      q hq P1FifthNamedParentActualIntegral.named_grid P1FifthNamedParentActualIntegral.named_mask
      P1FifthNamedParentActualIntegral.named_keys_injective hpositive e heQ ((e : ℝ) / 20) omega
      homega homegaRho rows4 licensed4 hgeometry (namedJ5 (refinedMesh q))
      (P1FifthNamedParentActualIntegral.named_family_gates e hcapQ q) (namedParent tag)
      (by cases tag <;> simp [namedParent, P1FifthNamedParentActualIntegral.namedRecords]) j hj
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset Bool)) (fun tag _ => hlocal tag)
  rw [Finset.sum_sub_distrib] at hsum
  have hcast : (namedSharpQ80Total : ℝ) =
      ∑ tag : Bool, ∑ c : ChildIndex, (childFloorQ tag c : ℝ) := by
    simp [namedSharpQ80Total]
  rw [← hcast] at hsum
  have hbound := (sub_le_sub_left hreserve.le (namedSharpQ80Total : ℝ)).trans hsum
  rw [P1FifthNamedParentActualIntegral.selected_namedJ5_eq e hcapQ
    ((e : ℝ) / 20) omega (refinedMesh q) hstep hw] at hbound
  have heq := P1FifthNamedParentActualIntegral.actual_selected_integral_eq_two_named_parents
    q hq e heQ hcapQ ((e : ℝ) / 20) omega hstep homega hw rows4 licensed4
  refine ⟨e, q, he, hecap, hq, hreserve, ?_⟩
  rw [heq]
  simpa [Fintype.sum_bool, namedParent, add_comm] using hbound

end
end ImbalancedChen.P5SharpQ80ActualFinitePolicy
