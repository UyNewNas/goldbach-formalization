import ImbalancedChen.P1ActualVariableFourthFifthCellTestLimit

/-!
SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

Exact complete-original-T3 source assembly for the corrected stored fifth
charge. Every next candidate is included before either own-cube gate; the
unchanged firstStop/raw-Q3 parent and target-divisor deletion remain literal.
Selected half-open owners partition the nonzero lookup difference exactly.
The positive cut is separated from a named signed actual small-coordinate
remainder before any limit is taken.

No stored h45 premise, retained-density identity, target convergence input,
or desired mean is assumed. A finite stored h45 check is separately required
before calling this causal charge a retained-polynomial difference. The
fixed-positive-cut limit here follows from the independently proved actual
producer cell limits; removal of the explicit small remainder remains OPEN.
The empty history / divisor one coefficient is never removed or reweighted.
-/

namespace ImbalancedChen.P1CorrectedFifthGlobalSourceAssembly

noncomputable section
open Filter Topology Set
open scoped Classical BigOperators
open P2OriginalFourthCapProducerInterface
open P1CorrectedFifthDensityDictionary P1CorrectedFifthCausalTupleDictionary
open P1ActualVariableFourthFifthCellTestLimit

abbrev FifthLabel (m : ℕ) := P1OriginalCoarseFifthContinuation.Label5 m

section FiniteSource

variable (D : HistoricalPrefixCapData) (J : Finset (FifthLabel D.m))
  (e : ℚ) (chi omega : ℝ) (rows : Finset ProducerRow) (licensed : ProducerRow → Prop)

def normalizedCharge (N cap : ℕ) : ℝ :=
  correctedStoredCharge D J e chi omega N cap ((N : ℝ) ^ (19 / 96 : ℝ)) rows licensed *
    Real.log (N : ℝ) / singularSeries N

def fullTupleCharge (N cap : ℕ) : ℝ :=
  ∑ p ∈ HistoricalThirdCoarse.P1OriginalCoarseFifth.candidates
      (e : ℝ) chi D.m omega N cap,
    (∏ i, 1 / ((p i : ℝ) - 1)) *
      correctedTupleDifference D J e chi omega rows licensed N cap p

def fullCellCharge (N cap : ℕ) (j : FifthLabel D.m) : ℝ :=
  ∑ p ∈ HistoricalThirdCoarse.P1OriginalCoarseFifth.candidates
      (e : ℝ) chi D.m omega N cap,
    (∏ i, 1 / ((p i : ℝ) - 1)) *
      (if actualPrimeTupleLog N p ∈ logPrimeMeshCell 0 (19 / 96) D.m j then
        correctedTupleDifference D J e chi omega rows licensed N cap p else 0)

/-- Actual small-coordinate tuples, with their original signed old/new
own-cube difference. This is not an absolute majorant or a discarded tail. -/
def smallCellRemainder (a : ℝ) (N cap : ℕ) (j : FifthLabel D.m) : ℝ :=
  ∑ p ∈ HistoricalThirdCoarse.P1OriginalCoarseFifth.candidates
      (e : ℝ) chi D.m omega N cap,
    (∏ i, 1 / ((p i : ℝ) - 1)) *
      (if (∃ i, actualPrimeTupleLog N p i < a) ∧
          actualPrimeTupleLog N p ∈ logPrimeMeshCell 0 (19 / 96) D.m j then
        correctedTupleDifference D J e chi omega rows licensed N cap p else 0)

def smallRemainder (a : ℝ) (N cap : ℕ) : ℝ :=
  ∑ j ∈ D.cells5 ∩ J, smallCellRemainder D J e chi omega rows licensed a N cap j

def positiveCharge (a : ℝ) (N cap : ℕ) : ℝ :=
  ∑ j ∈ D.cells5 ∩ J,
    correctedCellPrimeCorrection D J e chi omega rows licensed a N cap j

def selectedIntegral (a : ℝ) : ℝ :=
  ∑ j ∈ D.cells5 ∩ J, correctedSelectedStoredIntegral D e chi omega a j rows licensed

/-- Exact original-T3 normalization, with no restriction on N or levels. -/
theorem normalizedCharge_eq_fullTupleCharge (N cap : ℕ) :
    normalizedCharge D J e chi omega rows licensed N cap =
      fullTupleCharge D J e chi omega rows licensed N cap := by
  simpa only [normalizedCharge, fullTupleCharge,
    HistoricalThirdCoarse.P1OriginalCoarseFifth.candidates,
    originalT3_eq_historical] using
      corrected_charge_eq_tupleSum D J e chi omega rows licensed N cap
        ((N : ℝ) ^ (19 / 96 : ℝ))

/-- Exact pointwise support decomposition. Outside all selected owners
the corrected lookup equals its actual fourth ancestor and cancels. -/
theorem correctedDifference_eq_selected_owner_sum (N cap : ℕ) (p : Fin 5 → ℕ) :
    correctedTupleDifference D J e chi omega rows licensed N cap p =
      ∑ j ∈ D.cells5 ∩ J,
        if actualPrimeTupleLog N p ∈ logPrimeMeshCell 0 (19 / 96) D.m j then
          correctedTupleDifference D J e chi omega rows licensed N cap p else 0 := by
  by_cases hex : ∃ j ∈ D.cells5 ∩ J,
      actualPrimeTupleLog N p ∈ logPrimeMeshCell 0 (19 / 96) D.m j
  · obtain ⟨j, hj, ht⟩ := hex
    symm
    calc
      _ = if actualPrimeTupleLog N p ∈ logPrimeMeshCell 0 (19 / 96) D.m j then
          correctedTupleDifference D J e chi omega rows licensed N cap p else 0 := by
        apply Finset.sum_eq_single_of_mem j hj
        intro q _hq hqj
        apply if_neg
        intro hq
        exact hqj (logPrimeMeshCell_unique (by norm_num : (0 : ℝ) ≤ 19 / 96) hq ht)
      _ = _ := if_pos ht
  · have hout : ∀ j ∈ D.cells5 ∩ J,
        actualPrimeTupleLog N p ∉ logPrimeMeshCell 0 (19 / 96) D.m j := by
      simpa only [not_exists, not_and] using hex
    rw [correctedTupleDifference_outside D J e chi omega rows licensed N cap p hout]
    symm
    exact Finset.sum_eq_zero (fun j hj => if_neg (hout j hj))

/-- Finite sum exchange retains every original next candidate, including
those rejected by the OLD own cube and restored by the NEW own cube. -/
theorem fullTupleCharge_eq_sum_fullCells (N cap : ℕ) :
    fullTupleCharge D J e chi omega rows licensed N cap =
      ∑ j ∈ D.cells5 ∩ J, fullCellCharge D J e chi omega rows licensed N cap j := by
  unfold fullTupleCharge fullCellCharge
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _hp
  rw [correctedDifference_eq_selected_owner_sum D J e chi omega rows licensed N cap p,
    Finset.mul_sum]

/-- A mesh owner already supplies every strict upper cutoff t_i<rho.
Consequently this split is exact even before any prime-carrier hypothesis. -/
theorem fullCellCharge_eq_positive_add_small (a : ℝ) (N cap : ℕ) (j : FifthLabel D.m) :
    fullCellCharge D J e chi omega rows licensed N cap j =
      correctedCellPrimeCorrection D J e chi omega rows licensed a N cap j +
        smallCellRemainder D J e chi omega rows licensed a N cap j := by
  unfold fullCellCharge correctedCellPrimeCorrection smallCellRemainder
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p _hp
  by_cases ht : actualPrimeTupleLog N p ∈ logPrimeMeshCell 0 (19 / 96) D.m j
  · have hupper := logPrimeMeshCell_subset_box (by norm_num : (0 : ℝ) ≤ 19 / 96) D.m j ht
    by_cases hlo : ∀ i, a ≤ actualPrimeTupleLog N p i
    · have hb : actualPrimeTupleLog N p ∈
          logPrimeBox (fun _ : Fin 5 => a) (fun _ => (19 / 96 : ℝ)) :=
        mem_logPrimeBox.mpr (fun i => ⟨hlo i, (mem_logPrimeBox.mp hupper i).2⟩)
      have hn : ¬∃ i, actualPrimeTupleLog N p i < a := by
        rintro ⟨i, hi⟩
        exact not_lt_of_ge (hlo i) hi
      simp only [if_pos ht, Set.mem_inter_iff, hb, ht, and_self, if_true,
        hn, false_and, if_false, mul_zero, add_zero]
    · have hsmall : ∃ i, actualPrimeTupleLog N p i < a := by
        simpa only [not_forall, not_le] using hlo
      have hb : actualPrimeTupleLog N p ∉
          logPrimeBox (fun _ : Fin 5 => a) (fun _ => (19 / 96 : ℝ)) := by
        intro hb
        exact hlo (fun i => (mem_logPrimeBox.mp hb i).1)
      simp only [if_pos ht, Set.mem_inter_iff, hb, ht, false_and, if_false,
        hsmall, and_self, if_true, mul_zero, zero_add]
  · have hnot : actualPrimeTupleLog N p ∉
        logPrimeBox (fun _ : Fin 5 => a) (fun _ => (19 / 96 : ℝ)) ∩
          logPrimeMeshCell 0 (19 / 96) D.m j := fun h => ht h.2
    simp only [if_neg ht, if_neg hnot, ht, and_false, if_false, mul_zero, add_zero]

/-- The complete normalized corrected charge equals the selected positive
actual charges plus the explicit signed original small-coordinate remainder.
No h45 level order, integral approximation, or convergence is used. -/
theorem normalizedCharge_eq_positive_add_smallRemainder (a : ℝ) (N cap : ℕ) :
    normalizedCharge D J e chi omega rows licensed N cap =
      positiveCharge D J e chi omega rows licensed a N cap +
        smallRemainder D J e chi omega rows licensed a N cap := by
  rw [normalizedCharge_eq_fullTupleCharge, fullTupleCharge_eq_sum_fullCells]
  unfold positiveCharge smallRemainder
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _hj
  exact fullCellCharge_eq_positive_add_small D J e chi omega rows licensed a N cap j

/-- Genuine corrected full-charge-minus-explicit-remainder convergence
at every fixed positive cut. The limit uses the ACTUAL old producer profile. -/
theorem tendsto_normalizedCharge_sub_smallRemainder
    (a : ℝ) (ha : 0 < a) (haRho : a < (19 / 96 : ℝ))
    (howned : P1VariableFifthSelectedStoredBinding.OriginalOwnedRows D J e chi omega)
    (cap : ℕ → ℕ)
    (hcap : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      (N : ℝ) ^ (19 / 96 : ℝ) ≤ (cap N : ℝ)) :
    Tendsto (fun N : ℕ => normalizedCharge D J e chi omega rows licensed N (cap N) -
        smallRemainder D J e chi omega rows licensed a N (cap N))
      (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N})
      (𝓝 (selectedIntegral D J e chi omega rows licensed a)) := by
  have hlim := tendsto_corrected_selected_positive_actualCharge
    D J e chi omega a ha haRho rows licensed howned cap hcap
  apply hlim.congr'
  apply Eventually.of_forall
  intro N
  have hsplit := normalizedCharge_eq_positive_add_smallRemainder
    D J e chi omega rows licensed a N (cap N)
  change positiveCharge D J e chi omega rows licensed a N (cap N) = _
  linarith

end FiniteSource
end
end ImbalancedChen.P1CorrectedFifthGlobalSourceAssembly
