import ImbalancedChen.P1ActualCommonSixthWinnerSelectedTail
import ImbalancedChen.P2OriginalSixthCommonScheduleAndFullQ

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The compact source is the independently defined ORIGINAL target-deleted
six-prime tuple filter. Its frozen common CompactThirdChoice constructs
third support and the old actual retained leaf. The common constructor
then supplies a genuine strict sixth change and an attained winner.
No third-support, H5 guard, common upper guard, winner or licence is a
premise of this caller. The original row licence remains unchanged.
-/

namespace ImbalancedChen.P1CommonSixthCompactActualCaller

noncomputable section
open scoped Classical BigOperators
open P2OriginalFourthCapProducerInterface
open P2CompactThirdHistorySelection P2CompactOriginalRetainedSixth
open P2OriginalSixthCompactArithmeticFibre P2OriginalSixthCommonScheduleAndFullQ
open P2OriginalSixthSourceCompactCores
open P5OriginalCommonRefinedConstructor P5OriginalCommonRefinedPreservation
open P1CommonFifthElevenActualUpperGuard P1ActualCommonSixthWinnerSelectedTail
open Certificates.P2OriginalSixthElevenLogSemantics

def tupleHistory6 (p : Fin 6 → ℕ) : List ℕ := [p 5, p 4, p 3, p 2, p 1, p 0]

theorem tupleHistory6_log (N : ℕ) (p : Fin 6 → ℕ) :
    primeHistoryLogCoordinates (N : ℝ) 6 (tupleHistory6 p) = actualPrimeTupleLog N p := by
  ext i
  fin_cases i <;> rfl

/-- Real ORIGINAL compact tuples pay the actual common upper guard on
all eleven cells. A true old retained leaf supplies H5, approval-preserving
finite-max ancestry raises that bound to common actualParent5, and the
newly proved original-plane ceiling supplies the other direction. -/
theorem compact_original_tuple_common_sixth_admitted
    {n : ℕ} (D : CompactThirdChoice (commonCore n))
    (N cap : ℕ) (hN : 1 < N) (omega : ℝ) (homega : omega ≤ D.roughFloor)
    (hcap : (N : ℝ) ^ (19 / 96 : ℝ) ≤ (cap : ℝ))
    (rows4 : Finset ProducerRow) (licensedOriginal : ProducerRow → Prop)
    (J5 : Finset (P1OriginalVariableFifthContinuation.Label5 D.mesh))
    (rows5 : Finset (P1OriginalVariableFifthContinuation.FifthRow D.mesh))
    (c : Cell) (p : Fin 6 → ℕ) (hp : p ∈ compactTuples c n N) :
    let d := dataOfChoice D omega rows4 licensedOriginal J5 rows5
    actualParent5 d (N : ℝ) (tupleHistory6 p) ≤ oldCap c (actualPrimeTupleLog N p) ∧
      eligibleSixth d (N : ℝ) c (tupleHistory6 p) ∧
      actualParent5 d (N : ℝ) (tupleHistory6 p) < lambda6 d (N : ℝ) (tupleHistory6 p) ∧
      ∃ winner : Cell, eligibleSixth d (N : ℝ) winner (tupleHistory6 p) ∧
        lambda6 d (N : ℝ) (tupleHistory6 p) = newCap winner (actualPrimeTupleLog N p) := by
  dsimp only
  let d := dataOfChoice D omega rows4 licensedOriginal J5 rows5
  let history := tupleHistory6 p
  let Dc := restrictChoice D c
  have hsource := Finset.mem_filter.mp hp
  have hraw := Finset.mem_filter.mp hsource.1
  have hpi := mem_actualPrimeBoxTuples_iff.mp hraw.1
  have hc : PhysicalCell c (actualPrimeTupleLog N p) := hraw.2
  have hNr : (1 : ℝ) < N := by exact_mod_cast hN
  have hpos : ∀ q ∈ [p 5, p 4, p 3, p 2, p 1, p 0], 0 < q := by
    intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> exact (hpi _).1.pos
  have hcHistory : PhysicalCell c (primeHistoryLogCoordinates (N : ℝ) 6 history) := by
    rw [tupleHistory6_log]
    exact hc
  have hcore : primeHistoryLogCoordinates (N : ℝ) 6 history ∈ coreSequence c n := by
    rw [tupleHistory6_log]
    exact hsource.2
  have hs0 := actual_third_supported Dc N hN omega homega
    (p 0) (p 1) (p 2) (p 3) (p 4) (p 5) hpos c hcHistory hcore
  have hs : P1ThirdFallbackSupport.supported (d.e : ℝ) d.chi d.m d.omega (N : ℝ)
      (rosserAncestor 3 history) := by
    simpa [history, tupleHistory6, rosserAncestor, d, dataOfChoice, Dc, restrictChoice] using hs0
  have he : 0 ≤ d.e := D.e_pos.le
  have hlen : history.length = 6 := by simp [history, tupleHistory6]
  have hupper := actualParent5_le_oldCap_on_supported_source d (N : ℝ) he c history hlen hcHistory hs
  obtain ⟨oldLeaf, hleaf, hselected⟩ := compact_tuple_has_actual_retained_fibre c n Dc N cap hN
    omega homega hcap rows4 licensedOriginal J5 rows5 p hp (fun _ => 1)
  have hleafOld : oldLeaf ∈ firstExitRetainedLeaves
      (P1OriginalVariableFifthContinuation.policy5 d.e d.chi d.m d.omega (N : ℝ)
        d.rows4 d.licensed4 d.J5 d.rows5) (fun _ => 1) [] true 1
      (roughPrimeUniverse N cap ((N : ℝ) ^ omega) ((N : ℝ) ^ (19 / 96 : ℝ))) := hleaf
  have hlenOld : 6 ≤ oldLeaf.selected.length := by rw [hselected]; simp
  have hlowerOld := P1ActualOriginalAndCommonFifthGuard.original_actual_retained_H5_lower_guard
    d.e d.chi d.m d.omega d.rows4 d.licensed4 d.J5 d.rows5 N cap hNr
    ((N : ℝ) ^ omega) ((N : ℝ) ^ (19 / 96 : ℝ)) (fun _ => 1) oldLeaf hleafOld hlenOld
  have hselectedHistory : oldLeaf.selected = history := hselected
  rw [hselectedHistory] at hlowerOld
  have hself6 : rosserAncestor 6 history = history := rosserAncestor_self_of_length 6 history hlen
  rw [hself6] at hlowerOld
  have hraise := original_exponent5_le_common d (N : ℝ) (rosserAncestor 5 history)
  have hlower : H5 (primeHistoryLogCoordinates (N : ℝ) 6 history) < actualParent5 d (N : ℝ) history :=
    hlowerOld.trans_le hraise
  have helig : eligibleSixth d (N : ℝ) c history := ⟨hlen, hcHistory, hlower, hupper⟩
  have hchange := (eligibleSixth_actualParent_lt_newCap d (N : ℝ) c history helig).trans_le
    (eligibleSixth_newCap_le_lambda6 d (N : ℝ) c history helig)
  obtain ⟨winner, hwinElig, hwin⟩ := actual_sixth_improvement_has_winner d (N : ℝ) history hchange
  rw [tupleHistory6_log] at hupper hwin
  exact ⟨hupper, helig, hchange, winner, hwinElig, hwin⟩

end
end ImbalancedChen.P1CommonSixthCompactActualCaller
