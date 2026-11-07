import ImbalancedChen.CurrentP5MarkedTupleCommonRefinement

/-!
# Marked row witnesses inside one causal receiver cell

SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The marked source retains every witness coordinate and its row. Filtering a
single marked row by an additive-prime receiver label has the same count as
the corresponding original causal occurrence. This is a finite reindexing,
not an identification of a tuple physical cell with one additive receiver
cell. It makes no selected-cell density or coefficient-mass assertion.
-/

namespace ImbalancedChen.P5MarkedRowReceiverCellBridge

open scoped BigOperators

noncomputable section

/-- Row `i` witnesses with their original additive prime inside the
specified receiver cell. Distinct tuple witnesses remain distinct. -/
def markedRowReceiverCell {ι : Type*} [DecidableEq ι]
    (N : ℕ) (E : ℕ × ℕ → Prop) (label : ℕ → ι) (a : ι)
    (i : Fin 11) : Finset (ℕ × P5WitnessFour) :=
  (p5MarkedRowSource N E i).filter (fun t => label t.1 = a)

/-- Exact source equality before taking cardinalities. A receiver is
selected by its label; each of its row witnesses is retained separately. -/
theorem markedRowReceiverCell_eq_sigma {ι : Type*} [DecidableEq ι]
    (N : ℕ) (E : ℕ × ℕ → Prop) (label : ℕ → ι) (a : ι)
    (i : Fin 11) :
    markedRowReceiverCell N E label a i =
      ((p5CausalReceiverCell N label a).sigma
        (fun P => p5PaddedActualWitnesses N E (N - P) i)).image
          p5ConstantSigmaPair := by
  classical
  ext t
  rcases t with ⟨P, q⟩
  simp only [markedRowReceiverCell, Finset.mem_filter,
    mem_p5MarkedRowSource, mem_p5ConstantSigmaPair_image,
    mem_p5CausalReceiverCell]
  tauto

/-- The marked witness count in one row and one receiver cell is precisely
the original ordinary Upsilon occurrence count on that receiver cell. -/
theorem markedRowReceiverCell_card_eq_occurrence {ι : Type*} [DecidableEq ι]
    (N : ℕ) (E : ℕ × ℕ → Prop) (label : ℕ → ι) (a : ι)
    (i : Fin 11) :
    ((markedRowReceiverCell N E label a i).card : ℝ) =
      p5CausalCellOccurrence N E label a i := by
  classical
  rw [markedRowReceiverCell_eq_sigma,
    Finset.card_image_of_injective _ p5ConstantSigmaPair_injective,
    Finset.card_sigma, Nat.cast_sum]
  change (∑ P ∈ p5CausalReceiverCell N label a,
      ((p5PaddedActualWitnesses N E (N - P) i).card : ℝ)) =
    ∑ P ∈ p5CausalReceiverCell N label a,
      p5CausalReceiverOccurrence N E P i
  exact Finset.sum_congr rfl
    (fun P hP => p5PaddedActualWitnesses_card N E P i)

/-- The eleven signed row-cell counts reconstruct the literal receiver
ledger with its `3,1,-1,-1,1,1,-2,-1,-1,-1,-1` multiplicities. -/
theorem signed_markedRowReceiverCells_eq_causalLedger
    {ι : Type*} [DecidableEq ι]
    (N : ℕ) (E : ℕ × ℕ → Prop) (label : ℕ → ι) (a : ι) :
    (∑ i : Fin 11,
      ((markedRowReceiverCell N E label a i).card : ℝ) *
        p5CausalReceiverLedgerWeight i) =
      p5CausalCellSignedLedger N E label a := by
  simp_rw [markedRowReceiverCell_card_eq_occurrence]
  unfold p5CausalCellSignedLedger
  exact Finset.sum_congr rfl (fun i hi => mul_comm _ _)

end

end ImbalancedChen.P5MarkedRowReceiverCellBridge
