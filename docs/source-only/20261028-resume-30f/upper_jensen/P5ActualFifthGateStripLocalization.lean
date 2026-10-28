import ImbalancedChen.P1OriginalFifthCorrelatedDecodedGates
import ImbalancedChen.P5HistoricalIndexedTrimGeometry

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Actual endpoint gate rejection is localized on the ORIGINAL pointwise
support chamber, using the same mask, full-square and selected-square rows.
The pointwise-invalid region is explicitly retained, never called a wall.
-/
namespace ImbalancedChen.P5ActualFifthGateStripLocalization
noncomputable section
open Set MeasureTheory
open scoped Classical BigOperators
open VariableEnvelope P1OriginalVariableFifthContinuation
open P1OriginalPrefixRowDecodeSoundness P1OriginalFifthQuantitativeGateRefinement
open P1OriginalFifthCorrelatedRawBoxGates
open P1OriginalFifthGrid400RefinedFullBoxCover P1FifthUnitBoxGainDecomposition
open P1HistoricalFifthIndexedOwnerArchive P1HistoricalFifthIndexedBankError
open P1OriginalFifthAdoptedOwnerBank P5HistoricalIndexedTrimGeometry

def actualGap (I : Finset (Fin 5)) (p : Bool × Gate) : Affine5 :=
  (tentPlane I p.1).sub (gateAffine I p.2)

def pointwiseSupport (I : Finset (Fin 5)) : Set (Fin 5 → ℝ) :=
  {t | ∀ g : Gate, gateAllowed I g = true → (gateAffine I g).eval t < candidate 0 I t}

def unitCube : Set (Fin 5 → ℝ) := Set.univ.pi (fun _ => Icc (0 : ℝ) 1)

def actualGateStrips (I : Finset (Fin 5)) (delta : ℝ) : Set (Fin 5 → ℝ) :=
  unitCube ∩ {t | ∃ p ∈ gateRows I, |(actualGap I p).eval t| ≤ delta}

def rejectedSupportCore (i : ArchiveIndex) (e : ℚ) (q : ℕ) (chi omega : ℝ) : Set (Fin 5 → ℝ) :=
  gateRejectedDomain i e q chi omega ∩ pointwiseSupport (maskSlots 5 (archiveRow i).mask.toNat)

def rejectedInvalidCore (i : ArchiveIndex) (e : ℚ) (q : ℕ) (chi omega : ℝ) : Set (Fin 5 → ℝ) :=
  gateRejectedDomain i e q chi omega \ pointwiseSupport (maskSlots 5 (archiveRow i).mask.toNat)

theorem rejectedDomain_exact_partition (i : ArchiveIndex) (e : ℚ) (q : ℕ) (chi omega : ℝ) :
    gateRejectedDomain i e q chi omega =
      rejectedSupportCore i e q chi omega ∪ rejectedInvalidCore i e q chi omega := by
  ext t
  simp only [rejectedSupportCore, rejectedInvalidCore, mem_union, mem_inter_iff, mem_diff]
  tauto

theorem rejected_cores_disjoint (i : ArchiveIndex) (e : ℚ) (q : ℕ) (chi omega : ℝ) :
    Disjoint (rejectedSupportCore i e q chi omega) (rejectedInvalidCore i e q chi omega) :=
  Set.disjoint_left.mpr (fun _ hs hi => hi.2 hs.2)

theorem candidate_lower_endpoint_loss (m : ℕ) (r : FifthRow m)
    (t : Fin 5 → ℝ) (ht : t ∈ logPrimeMeshCell 0 (19 / 96) m r.cell) :
    candidate 0 r.selected t - (15 / 2 : ℝ) * (meshStepQ m : ℝ) ≤
      candidate 0 r.selected (fun i => (qLogPrimeMeshLo 0 (19 / 96) m r.cell i : ℝ)) := by
  let l := qLogPrimeMeshLo 0 (19 / 96) m r.cell
  change candidate 0 r.selected t - (15 / 2 : ℝ) * (meshStepQ m : ℝ) ≤
    candidate 0 r.selected (fun i => (l i : ℝ))
  have hlo (i : Fin 5) : (l i : ℝ) ≤ t i := by
    rw [show l i = qLogPrimeMeshLo 0 (19 / 96) m r.cell i from rfl,
      congrFun (cast_qLogPrimeMeshLo 0 (19 / 96) m r.cell) i]
    exact (mem_logPrimeMeshCell.mp ht i).1
  have hupper (i : Fin 5) : t i ≤ (l i : ℝ) + (meshStepQ m : ℝ) := by
    have hi := (mem_logPrimeMeshCell.mp ht i).2.le
    rw [← congrFun (cast_qLogPrimeMeshHi 0 (19 / 96) m r.cell) i] at hi
    simpa only [mesh_upper_eq_lower_add_step, Rat.cast_add] using hi
  have hsumlo : (∑ i ∈ r.selected, (l i : ℝ)) ≤ ∑ i ∈ r.selected, t i :=
    Finset.sum_le_sum (fun i _ => hlo i)
  have hcard : (r.selected.card : ℝ) ≤ 5 := by
    have hn : r.selected.card ≤ 5 := by
      simpa using (Finset.card_le_card (Finset.subset_univ r.selected))
    exact_mod_cast hn
  have hsumhi : (∑ i ∈ r.selected, t i) ≤
      (∑ i ∈ r.selected, (l i : ℝ)) + 5 * (meshStepQ m : ℝ) := by
    calc
      _ ≤ ∑ i ∈ r.selected, ((l i : ℝ) + (meshStepQ m : ℝ)) :=
        Finset.sum_le_sum (fun i _ => hupper i)
      _ = (∑ i ∈ r.selected, (l i : ℝ)) + r.selected.card * (meshStepQ m : ℝ) := by
        simp [Finset.sum_add_distrib]
      _ ≤ _ := add_le_add_left (mul_le_mul_of_nonneg_right hcard (by exact_mod_cast (meshStepQ_pos m).le)) _
  have hA := min_le_left (A (∑ i ∈ r.selected, t i)) (C (∑ i ∈ r.selected, t i))
  have hC := min_le_right (A (∑ i ∈ r.selected, t i)) (C (∑ i ∈ r.selected, t i))
  have hh : (0 : ℝ) ≤ (meshStepQ m : ℝ) := by exact_mod_cast (meshStepQ_pos m).le
  simp only [candidate, envelope_eq_v, v_eq_min, mul_zero, sub_zero]
  apply le_min <;> dsimp [A, C] at * <;> linarith

/-- A true pointwise margin exceeds the proved endpoint/mesh losses.
The original endpoint gate, not a newly defined checker, is concluded. -/
theorem gateCheck_of_pointwise_margins (e : ℚ) (m : ℕ) (r : FifthRow m)
    (t : Fin 5 → ℝ) (ht : t ∈ logPrimeMeshCell 0 (19 / 96) m r.cell)
    (hmargin : ∀ g : Gate, gateAllowed r.selected g = true →
      2 * (e : ℝ) + 32 * (meshStepQ m : ℝ) < candidate 0 r.selected t - (gateAffine r.selected g).eval t) :
    gateCheck e m r = true := by
  let l := qLogPrimeMeshLo 0 (19 / 96) m r.cell
  have hlow := candidate_lower_endpoint_loss m r t ht
  change candidate 0 r.selected t - (15 / 2 : ℝ) * (meshStepQ m : ℝ) ≤
    candidate 0 r.selected (fun i => (l i : ℝ)) at hlow
  have hh : (0 : ℝ) < (meshStepQ m : ℝ) := by exact_mod_cast meshStepQ_pos m
  have hlo (i : Fin 5) : (l i : ℝ) ≤ t i := by
    rw [show l i = qLogPrimeMeshLo 0 (19 / 96) m r.cell i from rfl,
      congrFun (cast_qLogPrimeMeshLo 0 (19 / 96) m r.cell) i]
    exact (mem_logPrimeMeshCell.mp ht i).1
  have hc : candidate (e : ℝ) r.selected (fun i => (l i : ℝ)) =
      candidate 0 r.selected (fun i => (l i : ℝ)) - 2 * (e : ℝ) := by simp [candidate]
  apply gateCheck_eq_true_of_lower_endpoint_margin e (17 * meshStepQ m) m r (by linarith [meshStepQ_pos m])
  · have hm := hmargin .half rfl
    rw [gateAffine, halfGate_eval] at hm
    have h : (1 / 2 : ℝ) + (17 * meshStepQ m : ℚ) ≤ candidate (e : ℝ) r.selected (fun i => (l i : ℝ)) := by
      push_cast
      linarith
    rw [← cast_lower_candidate e r.selected l] at h
    exact_mod_cast h
  · intro j
    have hm := hmargin (.full j) rfl
    rw [gateAffine, fullGate_eval] at hm
    have hmono := prefixSquareExpr_mono hlo j
    have h : prefixSquareExpr (fun i => (l i : ℝ)) j + (17 * meshStepQ m : ℚ) ≤
        candidate (e : ℝ) r.selected (fun i => (l i : ℝ)) := by push_cast; linarith
    rw [← cast_lower_candidate e r.selected l, ← cast_prefixSquareExpr l j] at h
    exact_mod_cast h
  · intro j hj
    have hallowed : gateAllowed r.selected (.selected j) = true := by simp [gateAllowed, hj]
    have hm := hmargin (.selected j) hallowed
    rw [gateAffine, selectedGate_eval] at hm
    have hmono := selectedSquareExpr_mono r.selected hlo j
    have h : selectedSquareExpr r.selected (fun i => (l i : ℝ)) j + (17 * meshStepQ m : ℚ) ≤
        candidate (e : ℝ) r.selected (fun i => (l i : ℝ)) := by push_cast; linarith
    rw [← cast_lower_candidate e r.selected l, ← cast_selectedSquareExpr r.selected l j] at h
    exact_mod_cast h

theorem rejected_gate_has_actual_affine_small_margin (e : ℚ) (m : ℕ) (r : FifthRow m)
    (t : Fin 5 → ℝ) (ht : t ∈ logPrimeMeshCell 0 (19 / 96) m r.cell)
    (hs : t ∈ pointwiseSupport r.selected) (hfail : gateCheck e m r = false) :
    ∃ p ∈ gateRows r.selected,
      |(actualGap r.selected p).eval t| ≤ 2 * (e : ℝ) + 32 * (meshStepQ m : ℝ) := by
  have hbad : ∃ g : Gate, gateAllowed r.selected g = true ∧
      candidate 0 r.selected t - (gateAffine r.selected g).eval t ≤
        2 * (e : ℝ) + 32 * (meshStepQ m : ℝ) := by
    by_contra hn
    push_neg at hn
    have hp := gateCheck_of_pointwise_margins e m r t ht hn
    rw [hfail] at hp
    contradiction
  obtain ⟨g, hg, hsmall⟩ := hbad
  have hpositive := hs g hg
  by_cases hside : A (∑ i ∈ r.selected, t i) ≤ C (∑ i ∈ r.selected, t i)
  · refine ⟨(false, g), by simp [gateRows, hg], ?_⟩
    have hcap : candidate 0 r.selected t = (tentPlane r.selected false).eval t := by
      simp [candidate, envelope_eq_v, v_eq_min, min_eq_left hside, tentPlane_eval]
    rw [actualGap, Affine5.eval_sub, ← hcap, abs_of_pos (sub_pos.mpr hpositive)]
    exact hsmall
  · refine ⟨(true, g), by simp [gateRows, hg], ?_⟩
    have hcap : candidate 0 r.selected t = (tentPlane r.selected true).eval t := by
      simp [candidate, envelope_eq_v, v_eq_min, min_eq_right (le_of_not_ge hside), tentPlane_eval]
    rw [actualGap, Affine5.eval_sub, ← hcap, abs_of_pos (sub_pos.mpr hpositive)]
    exact hsmall

theorem gateCheck_buffer_implies_zero (e : ℚ) (he : 0 ≤ e) (m : ℕ) (r : FifthRow m)
    (hc : gateCheck e m r = true) : gateCheck 0 m r = true := by
  have h := of_decide_eq_true hc
  apply decide_eq_true
  dsimp only [gateCheck] at *
  linarith

/-- Extra rejected owners on the genuine original pointwise support
chamber lie in actual 22-row proper-affine strips, without assuming any
rejected cost or volume bound. The complementary invalid core remains. -/
theorem rejectedSupportCore_subset_actual_strips (i : ArchiveIndex)
    (e : ℚ) (he : 0 ≤ e) (q : ℕ) (chi omega : ℝ) :
    rejectedSupportCore i e q chi omega ⊆
      actualGateStrips (maskSlots 5 (archiveRow i).mask.toNat)
        (2 * (e : ℝ) + 32 * (meshStepQ (refinedMesh q) : ℝ)) := by
  intro t ht
  obtain ⟨j, hj, htj⟩ := mem_iUnion₂.mp ht.1.1
  have hfail : gateCheck e (refinedMesh q) (sourceOwnerRow i q j) = false := by
    apply Bool.eq_false_iff.mpr
    intro hpass
    have hzero := gateCheck_buffer_implies_zero e he (refinedMesh q) (sourceOwnerRow i q j) hpass
    have hjStrict : j ∈ licensedOwners i e q chi omega := Finset.mem_filter.mpr ⟨hj, hzero, hpass⟩
    exact ht.1.2 (mem_iUnion₂.mpr ⟨j, hjStrict, htj⟩)
  have hmesh := htj.2.2.2.1
  refine ⟨?_, ?_⟩
  · have hp := gateRejected_subset_parent i e q chi omega ht.1
    intro k _
    have hk := mem_logPrimeBox.mp hp.2 k
    exact ⟨hk.1, by linarith [hk.2]⟩
  · exact rejected_gate_has_actual_affine_small_margin e (refinedMesh q)
      (sourceOwnerRow i q j) t hmesh ht.2 hfail

end
end ImbalancedChen.P5ActualFifthGateStripLocalization
