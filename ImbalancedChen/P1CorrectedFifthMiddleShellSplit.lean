import ImbalancedChen.P1CorrectedFifthGlobalSourceAssembly
import ImbalancedChen.P1OriginalFifthMiddleShellMovingLimit

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

Exact finite splitting of the CORRECTED fifth global remainder on its true
original T3 carrier. The actual variable-fourth old ancestor and corrected
stored new level remain in correctedTupleDifference throughout. No equality
with the distinct coarse old5 remainder is asserted.

correctedTupleDifference ALREADY includes log(N)/singularSeries(N). Thus
the shell and its absolute quadratic-moment bound require no second
normalization factor. OriginalOwnedRows proves the exact selected-owner
binding used to import the original-carrier moving shell moment.
-/

namespace ImbalancedChen.P1CorrectedFifthMiddleShellSplit

noncomputable section
open scoped Classical BigOperators
open P2OriginalFourthCapProducerInterface
open P1OriginalCoarseFifthContinuation
open P1CorrectedFifthCausalTupleDictionary
open P1OriginalFifthWeightedSourceReduction
open P1OriginalFifthMiddleShellBinMoment
open P1OriginalFifthMiddleShellFiniteBudget
open HistoricalThirdCoarse.P1OriginalCoarseFifth

/-- Exact owner-set equality follows from the actual original rough and
third-cell fields of OriginalOwnedRows. No owner equality is postulated. -/
theorem corrected_selected_owners_eq
    (D : HistoricalPrefixCapData) (J : Finset (Label5 D.m))
    (e : ℚ) (chi omega : ℝ)
    (howned : P1VariableFifthSelectedStoredBinding.OriginalOwnedRows D J e chi omega) :
    D.cells5∩J = selectedFifthCells e chi D.m omega (D.cells5∩J) := by
  ext j
  constructor
  · intro hj
    apply (mem_selectedFifthCells e chi D.m omega (D.cells5∩J) j).mpr
    exact ⟨hj,(howned.2.2 j hj).1,(howned.2.2 j hj).2⟩
  · intro hj
    exact ((mem_selectedFifthCells e chi D.m omega (D.cells5∩J) j).mp hj).1

section Finite
variable (D : HistoricalPrefixCapData) (J : Finset (Label5 D.m))
  (e : ℚ) (chi omega : ℝ) (rows : Finset ProducerRow) (licensed : ProducerRow→Prop)

def terminalCorrectedCell (a : ℝ) (N cap : ℕ) (j : Label5 D.m) : ℝ :=
  ∑ p∈(sourceCarrier e chi D.m omega N cap).filter
      (fun p => actualPrimeTupleLog N p 4<a),
    (∏ i,1/((p i:ℝ)-1)) *
      (if actualPrimeTupleLog N p∈logPrimeMeshCell 0 (19/96) D.m j then
        correctedTupleDifference D J e chi omega rows licensed N cap p else 0)

def correctedShellCell (delta a : ℝ) (N cap : ℕ) (j : Label5 D.m) : ℝ :=
  ∑ p∈shellCell e chi D.m omega delta a N cap j,
    (∏ i,1/((p i:ℝ)-1))*
      correctedTupleDifference D J e chi omega rows licensed N cap p

def correctedShell (delta a : ℝ) (N cap : ℕ) : ℝ :=
  ∑ j∈D.cells5∩J,correctedShellCell D J e chi omega rows licensed delta a N cap j

/-- The corrected source has the same exact terminal-face reduction,
proved from its original T3 strict order, independently of either level. -/
theorem corrected_smallCell_eq_terminal
    (a : ℝ) (N cap : ℕ) (hN : 1<N)
    (hcap : (N:ℝ)^(19/96:ℝ)≤(cap:ℝ)) (j : Label5 D.m) :
    P1CorrectedFifthGlobalSourceAssembly.smallCellRemainder
        D J e chi omega rows licensed a N cap j =
      terminalCorrectedCell D J e chi omega rows licensed a N cap j := by
  unfold P1CorrectedFifthGlobalSourceAssembly.smallCellRemainder terminalCorrectedCell
  simp only [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases ht : actualPrimeTupleLog N p∈logPrimeMeshCell 0 (19/96) D.m j
  · have hd := (mem_candidates_iff_log_on_cell (e:ℝ) chi D.m omega
      N cap hN hcap p j ht).mp hp
    have hanti := ((mem_jointRegion (e:ℝ) chi D.m omega j _).mp hd.2).2.1
    have hface : (∃ i,actualPrimeTupleLog N p i<a) ↔ actualPrimeTupleLog N p 4<a := by
      constructor
      · exact P1OriginalFifthAllFacesAnalyticTail.last_lt_of_any_coordinate_lt _ hanti
      · intro hh
        exact ⟨4,hh⟩
    simp [ht,hface]
  · simp [ht]

/-- The signed corrected difference is split exactly at the chosen
terminal lower cutoff. No positivity or stored level-order check is used. -/
theorem corrected_smallCell_split
    (delta a : ℝ) (hda : delta≤a) (N cap : ℕ) (hN : 1<N)
    (hcap : (N:ℝ)^(19/96:ℝ)≤(cap:ℝ)) (j : Label5 D.m) :
    P1CorrectedFifthGlobalSourceAssembly.smallCellRemainder
        D J e chi omega rows licensed a N cap j =
      P1CorrectedFifthGlobalSourceAssembly.smallCellRemainder
        D J e chi omega rows licensed delta N cap j +
      correctedShellCell D J e chi omega rows licensed delta a N cap j := by
  rw [corrected_smallCell_eq_terminal D J e chi omega rows licensed a N cap hN hcap j,
    corrected_smallCell_eq_terminal D J e chi omega rows licensed delta N cap hN hcap j]
  unfold terminalCorrectedCell correctedShellCell shellCell
  simp only [Finset.sum_filter]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p _
  by_cases ht : actualPrimeTupleLog N p∈logPrimeMeshCell 0 (19/96) D.m j
  · by_cases hd : actualPrimeTupleLog N p 4<delta
    · have ha : actualPrimeTupleLog N p 4<a := hd.trans_le hda
      have hnd : ¬delta≤actualPrimeTupleLog N p 4 := not_le_of_gt hd
      simp [ht,hd,ha,hnd]
    · have hdl : delta≤actualPrimeTupleLog N p 4 := le_of_not_gt hd
      by_cases ha : actualPrimeTupleLog N p 4<a <;> simp [ht,hd,hdl,ha]
  · simp [ht]

/-- Exact corrected R(a)=corrected R(delta)+the actual signed shell on
the ORIGINAL selected D.cells5 intersection J owners. -/
theorem corrected_smallRemainder_split
    (delta a : ℝ) (hda : delta≤a) (N cap : ℕ) (hN : 1<N)
    (hcap : (N:ℝ)^(19/96:ℝ)≤(cap:ℝ)) :
    P1CorrectedFifthGlobalSourceAssembly.smallRemainder
        D J e chi omega rows licensed a N cap =
      P1CorrectedFifthGlobalSourceAssembly.smallRemainder
        D J e chi omega rows licensed delta N cap +
      correctedShell D J e chi omega rows licensed delta a N cap := by
  unfold P1CorrectedFifthGlobalSourceAssembly.smallRemainder correctedShell
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  exact corrected_smallCell_split D J e chi omega rows licensed delta a hda N cap hN hcap j

/-- A tuplewise estimate for the already-normalized CORRECTED difference
is transported to the true original-carrier quadratic shell moment. -/
theorem correctedShellCell_abs_le_quadraticMoment
    (delta a : ℝ) (ha : 0<a) (N cap : ℕ) (hN : 1<N)
    (hcap : (N:ℝ)^(19/96:ℝ)≤(cap:ℝ))
    (howned : P1VariableFifthSelectedStoredBinding.OriginalOwnedRows D J e chi omega)
    (j : Label5 D.m) (hj : j∈D.cells5∩J) (C : ℝ)
    (hpoint : ∀ p∈shellCell e chi D.m omega delta a N cap j,
      |correctedTupleDifference D J e chi omega rows licensed N cap p| ≤
        C*(actualPrimeTupleLog N p 4)^2) :
    |correctedShellCell D J e chi omega rows licensed delta a N cap j| ≤
      C*shellMoment e chi D.m omega delta a N cap j := by
  have hsel : j∈selectedFifthCells e chi D.m omega (D.cells5∩J) := by
    rw [← corrected_selected_owners_eq D J e chi omega howned]
    exact hj
  unfold correctedShellCell shellMoment
  rw [Finset.mul_sum]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro p hp
  let r := owner a N p
  have hpbin : p∈shellBin e chi D.m omega delta a N cap j r :=
    Finset.mem_filter.mpr ⟨hp,rfl⟩
  have hw := actualPrimeBoxWeight_nonneg
    (shellBin_subset_prime_box e chi D.m omega delta a ha (D.cells5∩J)
      N cap hN hcap j hsel r hpbin)
  rw [abs_mul,abs_of_nonneg hw]
  have hh := mul_le_mul_of_nonneg_left (hpoint p hp) hw
  convert hh using 1 <;> ring

/-- Every selected corrected owner is counted once, without asserting
that an arbitrary historical cap table has the original policy geometry. -/
theorem correctedShell_abs_le_sum_quadraticMoments
    (delta a : ℝ) (ha : 0<a) (N cap : ℕ) (hN : 1<N)
    (hcap : (N:ℝ)^(19/96:ℝ)≤(cap:ℝ))
    (howned : P1VariableFifthSelectedStoredBinding.OriginalOwnedRows D J e chi omega)
    (C : ℝ)
    (hpoint : ∀ j∈D.cells5∩J,
      ∀ p∈shellCell e chi D.m omega delta a N cap j,
      |correctedTupleDifference D J e chi omega rows licensed N cap p| ≤
        C*(actualPrimeTupleLog N p 4)^2) :
    |correctedShell D J e chi omega rows licensed delta a N cap| ≤
      C*∑ j∈D.cells5∩J,shellMoment e chi D.m omega delta a N cap j := by
  unfold correctedShell
  rw [Finset.mul_sum]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro j hj
  exact correctedShellCell_abs_le_quadraticMoment D J e chi omega rows licensed
    delta a ha N cap hN hcap howned j hj C (hpoint j hj)

end Finite
end
end ImbalancedChen.P1CorrectedFifthMiddleShellSplit
