import ImbalancedChen.P2OriginalSixthSourceLossConvergence

/-!
SOURCE ONLY / UNCOMPILED_ZERO_CREDIT.

The compact source is a filter of the SAME original target-deleted prime
tuple source.  Every compact tuple constructs an actual policy5 retained
leaf over the same original rough universe.  Arbitrary signed tuple tests
split exactly into compact and omitted-source terms.  No replacement of a
signed coefficient by its absolute value or a numerical gain is made.
-/

namespace ImbalancedChen.P2OriginalSixthCompactArithmeticFibre

noncomputable section
open Classical
open scoped BigOperators
open Certificates.P2OriginalSixthElevenLogSemantics
open P2OriginalFourthCapProducerInterface P1OriginalVariableFifthContinuation
open P2CompactThirdHistorySelection P2CompactOriginalRetainedSixth
open P2OriginalSixthSourceCompactCores

def originalTuples (c : Cell) (N : ℕ) : Finset (Fin 6 → ℕ) :=
  (actualPrimeBoxTuples N (fun _ : Fin 6 => (0 : ℝ)) (fun _ => (19 / 96 : ℝ))).filter
    (fun p => PhysicalCell c (actualPrimeTupleLog N p))

def compactTuples (c : Cell) (n N : ℕ) : Finset (Fin 6 → ℕ) :=
  (originalTuples c N).filter (fun p => actualPrimeTupleLog N p ∈ coreSequence c n)

def omittedTuples (c : Cell) (n N : ℕ) : Finset (Fin 6 → ℕ) :=
  (originalTuples c N).filter (fun p => actualPrimeTupleLog N p ∉ coreSequence c n)

/-- The original source is partitioned before any arithmetic test is
evaluated.  F may be signed or contain the exact count-minus-coprime-mean. -/
theorem original_signed_sum_split (c : Cell) (n N : ℕ) (F : (Fin 6 → ℕ) → ℝ) :
    (∑ p ∈ originalTuples c N, F p) =
      (∑ p ∈ compactTuples c n N, F p) + (∑ p ∈ omittedTuples c n N, F p) := by
  unfold compactTuples omittedTuples
  rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p _
  by_cases hp : actualPrimeTupleLog N p ∈ coreSequence c n <;> simp [hp]

/-- These are actual source tuples, not arbitrary prime lists satisfying
an assumed carrier licence.  Compactness/table, third support, history
allowance, first-four validity and same-carrier sublist have all been
constructed in the preceding source modules. -/
theorem compact_tuple_has_actual_retained_fibre
    (c : Cell) (n : ℕ) (D : CompactThirdChoice (coreSequence c n))
    (N cap : ℕ) (hN : 1 < N) (omega : ℝ) (homega : omega ≤ D.roughFloor)
    (hcap : (N : ℝ)^(19 / 96 : ℝ) ≤ (cap : ℝ))
    (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
    (J5 : Finset (Label5 D.mesh)) (rows5 : Finset (FifthRow D.mesh))
    (p : Fin 6 → ℕ) (hp : p ∈ compactTuples c n N) (h : ℕ → ℝ) :
    ∃ leaf ∈ firstExitRetainedLeaves
      (policy5 D.e D.chi D.mesh omega (N : ℝ) rows4 licensed4 J5 rows5) h [] true 1
      (roughPrimeUniverse N cap ((N : ℝ)^omega) ((N : ℝ)^(19 / 96 : ℝ))),
      leaf.selected = [p 5,p 4,p 3,p 2,p 1,p 0] := by
  have hsource := Finset.mem_filter.mp hp
  have hraw := Finset.mem_filter.mp hsource.1
  have hpi := mem_actualPrimeBoxTuples_iff.mp hraw.1
  have hc : PhysicalCell c (actualPrimeTupleLog N p) := hraw.2
  have hpos : ∀ i, 0 < p i := fun i => (hpi i).1.pos
  have hNr : (1 : ℝ) < N := by exact_mod_cast hN
  have hlog_lt (i j : Fin 6) (hij : actualPrimeTupleLog N p i < actualPrimeTupleLog N p j) :
      p i < p j := by
    have hh := (Real.rpow_lt_rpow_left_iff hNr).mpr hij
    rw [actualPrimeTupleLog_rpow hN p hpos i, actualPrimeTupleLog_rpow hN p hpos j] at hh
    exact_mod_cast hh
  have h65 : p 5 < p 4 := hlog_lt 5 4 hc.order.1
  have h54 : p 4 < p 3 := hlog_lt 4 3 hc.order.2.1
  have h43 : p 3 < p 2 := hlog_lt 3 2 hc.order.2.2.1
  have h32 : p 2 < p 1 := hlog_lt 2 1 hc.order.2.2.2.1
  have h21 : p 1 < p 0 := hlog_lt 1 0 hc.order.2.2.2.2
  have hprime : ∀ q ∈ [p 0,p 1,p 2,p 3,p 4,p 5], q.Prime := by
    intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> exact (hpi _).1
  have hdelete : ∀ q ∈ [p 0,p 1,p 2,p 3,p 4,p 5], ¬q ∣ N := by
    intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> exact (hpi _).2.1
  have hcoords : primeHistoryLogCoordinates (N : ℝ) 6 [p 5,p 4,p 3,p 2,p 1,p 0] =
      actualPrimeTupleLog N p := by
    ext i
    fin_cases i <;> rfl
  have hc' : PhysicalCell c
      (primeHistoryLogCoordinates (N : ℝ) 6 [p 5,p 4,p 3,p 2,p 1,p 0]) := by
    rw [hcoords]
    exact hc
  have ht' : primeHistoryLogCoordinates (N : ℝ) 6 [p 5,p 4,p 3,p 2,p 1,p 0] ∈
      coreSequence c n := by
    rw [hcoords]
    exact hsource.2
  exact exists_same_carrier_retained_sixth D N cap hN omega homega hcap
    rows4 licensed4 J5 rows5 (p 0) (p 1) (p 2) (p 3) (p 4) (p 5)
    hprime hdelete h65 h54 h43 h32 h21 c hc' ht' h

end
end ImbalancedChen.P2OriginalSixthCompactArithmeticFibre
