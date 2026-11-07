import ImbalancedChen.P5AllChildrenReserveReassembly
import ImbalancedChen.P5NamedAllChildrenSelectedJensen
import ImbalancedChen.P1OriginalFifthJointMeshSchedule
import ImbalancedChen.P1FifthNamedParentActualIntegral

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
The two original STRICT-margin parent boxes have actual full selected-owner
coverage on one common buffered complete mesh. Thus their omitted sets
are EMPTY, not merely bounded by an assumed small target volume. Their
all64 reserves pay each raw modulus once and can be made arbitrarily small.
The full historical archive bank is not identified with these two rows.
-/
namespace ImbalancedChen.P5NamedOwnerReserveArbitraryTolerance
noncomputable section
open Set MeasureTheory
open scoped Classical BigOperators
open P1OriginalPrefixRowDecodeSoundness
open P1OriginalVariableFifthContinuation
open P1OriginalFifthGrid400RefinedFullBoxCover
open P1FifthMask6NamedParent0Owner P1FifthMask5NamedParent1Owner
open P1FifthNamedParentsConcreteJ5
open P1FifthUnitBoxGainDecomposition
open P1FifthGrid400UnitBoxPartition
open P2OriginalFourthCapProducerInterface
open P5NamedFifthPayloadSemantics
open P5NamedFifthAllChildren
open P5OldFifthExact64ChildTiling
open P5ChildSelectedOwnerJensenReserve
open P5NamedAllChildrenSelectedJensen
open P5AllChildrenReserveReassembly
open P1OriginalFifthLiteralKernelModulus
open P1OriginalFifthJointMeshSchedule

abbrev Point := Fin 5 → ℝ

theorem named_mask_nonneg (tag : Bool) : 0 ≤ (namedParent tag).mask := by
  cases tag <;> norm_num [namedParent, selectedParent0, selectedParent1]

theorem named_parent_subset_ambient (tag : Bool) :
    (namedParent tag).originalBox ⊆
      logPrimeBox (fun _ : Fin 5 => (0 : ℝ)) (fun _ => (19 / 96 : ℝ)) := by
  intro t ht
  apply mem_logPrimeBox.mpr
  intro i
  have hlo : (0 : ℝ) ≤ ((namedParent tag).lower i : ℝ) := by
    cases tag <;> fin_cases i <;>
      norm_num [namedParent, selectedParent0, selectedParent1, FifthWireRow.lower]
  exact ⟨hlo.trans (ht i).1, (ht i).2.trans_le (named_upper_bound tag i)⟩

/-- The actual original firstStop/third-owner proofs and complete decoded
cover license every point of the literal raw parent. No selected-domain
identity or omitted-volume estimate is assumed. -/
theorem named_rawRetained_eq_parent (tag : Bool)
    (e : ℚ) (he : 0 < e) (hemax : e ≤ 3 / 51200)
    (chi omega : ℝ) (hchi : chi < (e : ℝ) / 10)
    (m : ℕ) (hstep : logPrimeMeshStep 0 (19 / 96) m ≤ chi)
    (hw : omega ≤ 1 / 400)
    (hcover : (namedParent tag).originalBox ∩
        logPrimeBox (fun _ : Fin 5 => (0 : ℝ)) (fun _ => (19 / 96 : ℝ)) =
      ⋃ r ∈ decodeFifthRows (namedParent tag) m,
        logPrimeMeshCell 0 (19 / 96) m r.cell) :
    rawRetained (namedParent tag) e chi m omega (namedJ5 m) = (namedParent tag).originalBox := by
  apply Set.Subset.antisymm inter_subset_left
  intro t ht
  have hpoint : t ∈ (namedParent tag).originalBox ∩
      logPrimeBox (fun _ : Fin 5 => (0 : ℝ)) (fun _ => (19 / 96 : ℝ)) :=
    ⟨ht, named_parent_subset_ambient tag ht⟩
  rw [hcover] at hpoint
  obtain ⟨r, hr, hmesh⟩ := mem_iUnion₂.mp hpoint
  have hsel : r.cell ∈ P1OriginalCoarseFifthContinuation.selectedFifthCells
      e chi m omega (namedJ5 m) := by
    cases tag
    · exact parent0_mem_selected_namedJ5 e hemax chi omega m hstep hw r hr
    · exact parent1_mem_selected_namedJ5 e hemax chi omega m hstep hw r hr
  have howner : t ∈ rawOwnerDomain (namedParent tag) e chi m omega r.cell := by
    cases tag
    · exact parent0_namedJ5_rawOwnerDomain e he hemax chi omega hchi m hstep hw r hr t hmesh
    · exact parent1_namedJ5_rawOwnerDomain e he hemax chi omega hchi m hstep hw r hr t hmesh
  exact ⟨ht, mem_iUnion₂.mpr ⟨r.cell, hsel, howner.2⟩⟩

theorem named_retainedChild_eq_child (tag : Bool)
    (e : ℚ) (he : 0 < e) (hemax : e ≤ 3 / 51200)
    (chi omega : ℝ) (hchi : chi < (e : ℝ) / 10)
    (m : ℕ) (hstep : logPrimeMeshStep 0 (19 / 96) m ≤ chi)
    (hw : omega ≤ 1 / 400)
    (hcover : (namedParent tag).originalBox ∩
        logPrimeBox (fun _ : Fin 5 => (0 : ℝ)) (fun _ => (19 / 96 : ℝ)) =
      ⋃ r ∈ decodeFifthRows (namedParent tag) m,
        logPrimeMeshCell 0 (19 / 96) m r.cell)
    (c : ChildIndex) :
    retainedChild (namedParent tag) c e chi m omega (namedJ5 m) = childBox (namedParent tag) c := by
  apply Set.Subset.antisymm inter_subset_left
  intro t ht
  have hraw := child_subset_parent (namedParent tag) (P5NamedFifthAllChildren.named_grid tag) c ht
  have hret : t ∈ rawRetained (namedParent tag) e chi m omega (namedJ5 m) := by
    rw [named_rawRetained_eq_parent tag e he hemax chi omega hchi m hstep hw hcover]
    exact hraw
  exact ⟨ht, hret.2⟩

theorem named_omittedChild_empty (tag : Bool)
    (e : ℚ) (he : 0 < e) (hemax : e ≤ 3 / 51200)
    (chi omega : ℝ) (hchi : chi < (e : ℝ) / 10)
    (m : ℕ) (hstep : logPrimeMeshStep 0 (19 / 96) m ≤ chi)
    (hw : omega ≤ 1 / 400)
    (hcover : (namedParent tag).originalBox ∩
        logPrimeBox (fun _ : Fin 5 => (0 : ℝ)) (fun _ => (19 / 96 : ℝ)) =
      ⋃ r ∈ decodeFifthRows (namedParent tag) m,
        logPrimeMeshCell 0 (19 / 96) m r.cell)
    (c : ChildIndex) :
    omittedChild (namedParent tag) c e chi m omega (namedJ5 m) = ∅ := by
  simp only [omittedChild,
    named_retainedChild_eq_child tag e he hemax chi omega hchi m hstep hw hcover c,
    sdiff_self]

/-- All64 reserves are exactly one raw modulus divided by400^5. There is
neither a decoded-owner multiplier nor a factor64 raw mass charge. -/
theorem named_all64_reserve_eq_one_raw_modulus (tag : Bool)
    (e : ℚ) (he : 0 < e) (hemax : e ≤ 3 / 51200)
    (chi omega : ℝ) (hchi : chi < (e : ℝ) / 10)
    (m : ℕ) (hstep : logPrimeMeshStep 0 (19 / 96) m ≤ chi)
    (hw : omega ≤ 1 / 400)
    (hcover : (namedParent tag).originalBox ∩
        logPrimeBox (fun _ : Fin 5 => (0 : ℝ)) (fun _ => (19 / 96 : ℝ)) =
      ⋃ r ∈ decodeFifthRows (namedParent tag) m,
        logPrimeMeshCell 0 (19 / 96) m r.cell) :
    namedReserveTotal tag e chi m omega (namedJ5 m) =
      rowModulus (namedParent tag) e / (400 : ℝ)^5 := by
  have hr := named_rawRetained_eq_parent tag e he hemax chi omega hchi m hstep hw hcover
  have ho : rawOmitted (namedParent tag) e chi m omega (namedJ5 m) = ∅ := by
    simp only [rawOmitted, hr, sdiff_self]
  have hv0 : volume.real (∅ : Set Point) = 0 := by simp [Measure.real]
  unfold namedReserveTotal
  rw [sum64_reserve_eq_single_raw_reserve (namedParent tag)
    (P5NamedFifthAllChildren.named_grid tag), ho, hv0, mul_zero, zero_add, hr,
    rawBox_real_volume (namedParent tag) (P5NamedFifthAllChildren.named_grid tag)]
  ring

/-- One rational buffer is chosen BEFORE one complete common mesh. The
actual128 omitted sets are empty and the total reserve is below eta.
The table is the explicitly chosen local namedJ5, fixed before N. -/
theorem exists_named_common_policy_reserve_lt
    (eta omega : ℝ) (heta : 0 < eta) (homega : 0 < omega) (hw : omega ≤ 1 / 400) :
    ∃ e : ℚ, ∃ q : ℕ,
      0 < (e : ℝ) ∧ (e : ℝ) < 3 / 51200 ∧ 0 < q ∧
      logPrimeMeshStep 0 (19 / 96) (refinedMesh q) ≤ (e : ℝ) / 20 ∧
      logPrimeMeshStep 0 (19 / 96) (refinedMesh q) ≤ omega / 2 ∧
      (∀ tag : Bool, ∀ c : ChildIndex,
        omittedChild (namedParent tag) c e ((e : ℝ) / 20) (refinedMesh q) omega
          (namedJ5 (refinedMesh q)) = ∅) ∧
      (∑ tag : Bool, namedReserveTotal tag e ((e : ℝ) / 20) (refinedMesh q) omega
        (namedJ5 (refinedMesh q))) < eta := by
  let modulus : Bool → ℝ → ℝ := fun tag => rowModulus (namedParent tag)
  let mass : Bool → ℝ := fun tag => rowMassBound (namedParent tag)
  obtain ⟨e, q, he, hecap, hq, _, hchi, hstep, hstepOmega, hbudget, hcover⟩ :=
    exists_joint_buffer_mesh_complete_cover (Finset.univ : Finset Bool) modulus mass
      (fun tag _ => (rowModulus_continuous (namedParent tag)).continuousAt)
      (fun tag _ => rowModulus_zero (namedParent tag)) eta omega heta homega
  have heQ : 0 < e := by exact_mod_cast he
  have hcapQ : e ≤ 3 / 51200 := by exact_mod_cast hecap.le
  have hcoverNamed (tag : Bool) := hcover (namedParent tag)
    (P5NamedFifthAllChildren.named_grid tag) (named_mask_nonneg tag)
  have hzero (tag : Bool) (c : ChildIndex) := named_omittedChild_empty tag e heQ hcapQ
    ((e : ℝ) / 20) omega hchi (refinedMesh q) hstep hw (hcoverNamed tag) c
  have hres (tag : Bool) := named_all64_reserve_eq_one_raw_modulus tag e heQ hcapQ
    ((e : ℝ) / 20) omega hchi (refinedMesh q) hstep hw (hcoverNamed tag)
  have hsum : (∑ tag : Bool, namedReserveTotal tag e ((e : ℝ) / 20) (refinedMesh q) omega
      (namedJ5 (refinedMesh q))) ≤ bankEnvelope (Finset.univ : Finset Bool) modulus mass e := by
    unfold bankEnvelope
    apply Finset.sum_le_sum
    intro tag _
    rw [hres tag]
    change rowModulus (namedParent tag) e / (400 : ℝ)^5 ≤
      rowModulus (namedParent tag) e / (400 : ℝ)^5 +
        rowMassBound (namedParent tag) * (428 / 75 : ℝ) * (e : ℝ) / (400 : ℝ)^4
    have hM : 0 ≤ rowMassBound (namedParent tag) := by
      linarith [one_le_rowMassBound (namedParent tag)]
    exact le_add_of_nonneg_right (by positivity)
  exact ⟨e, q, he, hecap, hq, hstep, hstepOmega, hzero, hsum.trans_lt hbudget⟩

/-- A finite actual local named policy attains the symbolic all128 Jensen
sum to within ANY prescribed loss. The actual variable fourth parent and
all original geometry/licence premises remain; no target integral supplier
is assumed. This is still not a theorem about the full archived row bank. -/
theorem exists_named_actual_integral_ge_Jensen_sub_tolerance
    (eta omega : ℝ) (heta : 0 < eta) (homega : 0 < omega) (hw : omega ≤ 1 / 400)
    (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
    (hgeometry : ∀ r ∈ rows4, licensed4 r → r.Geometry) :
    ∃ e : ℚ, ∃ q : ℕ,
      0 < (e : ℝ) ∧ (e : ℝ) < 3 / 51200 ∧ 0 < q ∧
      (∑ tag : Bool, namedReserveTotal tag e ((e : ℝ) / 20) (refinedMesh q) omega
        (namedJ5 (refinedMesh q))) < eta ∧
      (∑ tag : Bool, namedCertifiedTotal tag) - eta ≤
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
  have hlocal (tag : Bool) := named_all64_Jensen_minus_reserve_le_actual_owner_sum
    P1FifthNamedParentActualIntegral.namedRecords q hq
    P1FifthNamedParentActualIntegral.named_grid P1FifthNamedParentActualIntegral.named_mask
    P1FifthNamedParentActualIntegral.named_keys_injective hpositive e heQ ((e : ℝ) / 20) omega
    homega homegaRho rows4 licensed4 hgeometry (namedJ5 (refinedMesh q))
    (P1FifthNamedParentActualIntegral.named_family_gates e hcapQ q) tag (by
      cases tag <;> simp [namedParent, P1FifthNamedParentActualIntegral.namedRecords])
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset Bool)) (fun tag _ => hlocal tag)
  rw [Finset.sum_sub_distrib] at hsum
  have hbound := (sub_le_sub_left hreserve.le (∑ tag : Bool, namedCertifiedTotal tag)).trans hsum
  rw [P1FifthNamedParentActualIntegral.selected_namedJ5_eq e hcapQ
    ((e : ℝ) / 20) omega (refinedMesh q) hstep hw] at hbound
  have heq := P1FifthNamedParentActualIntegral.actual_selected_integral_eq_two_named_parents
    q hq e heQ hcapQ ((e : ℝ) / 20) omega hstep homega hw rows4 licensed4
  refine ⟨e, q, he, hecap, hq, hreserve, ?_⟩
  rw [heq]
  simpa [Fintype.sum_bool, namedParent, add_comm] using hbound

end
end ImbalancedChen.P5NamedOwnerReserveArbitraryTolerance
