import ImbalancedChen.P1OriginalFifthMiddleShellMovingLimit

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

An exact finite splitting of the SAME original coarse fifth remainder:
R(a)=R(delta)+the signed shell delta<=t5<a. The actual original coarse
old5, cap5, selected labels, rank-four first-exit carrier and all T3 gates
are preserved. No corrected variable-old parent is substituted here.

The finite triangle theorem consumes a tuplewise normalized difference
estimate and the already established actual quadratic shell moment. It
does not assume a shell sum or a final remainder estimate.
-/

namespace ImbalancedChen.P1OriginalFifthMiddleShellRemainderSplit

noncomputable section
open scoped Classical BigOperators
open P1OriginalCoarseFifthContinuation
open HistoricalThirdCoarse.P1OriginalCoarseFifth
open P1OriginalFifthWeightedSourceReduction
open P1OriginalFifthMiddleShellBinMoment
open P1OriginalFifthMiddleShellFiniteBudget

def cellDifference (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (J4 : Finset (Label4 m)) (cap4 : Label4 m → ℚ)
    (cap5 : Label5 m → ℚ) (N cap : ℕ) (j : Label5 m) (p : Tuple) : ℝ :=
  actualPrimeTupleOwnCubeMinus N cap (cap5 j:ℝ) p -
    actualPrimeTupleOwnCubeMinus N cap (old5 e chi m omega J4 cap4 j:ℝ) p

def terminalCellRemainder (e : ℚ) (chi : ℝ) (m : ℕ) (omega a : ℝ)
    (J4 : Finset (Label4 m)) (cap4 : Label4 m → ℚ)
    (cap5 : Label5 m → ℚ) (N cap : ℕ) (j : Label5 m) : ℝ :=
  ∑ p ∈ (sourceCarrier e chi m omega N cap).filter
      (fun p => actualPrimeTupleLog N p 4<a),
    (∏ i,1/((p i:ℝ)-1)) *
      (if actualPrimeTupleLog N p∈logPrimeMeshCell 0 (19/96) m j then
        cellDifference e chi m omega J4 cap4 cap5 N cap j p else 0)

def signedShellCell (e : ℚ) (chi : ℝ) (m : ℕ) (omega delta a : ℝ)
    (J4 : Finset (Label4 m)) (cap4 : Label4 m → ℚ)
    (cap5 : Label5 m → ℚ) (N cap : ℕ) (j : Label5 m) : ℝ :=
  ∑ p ∈ shellCell e chi m omega delta a N cap j,
    (∏ i,1/((p i:ℝ)-1))*cellDifference e chi m omega J4 cap4 cap5 N cap j p

def signedShell (e : ℚ) (chi : ℝ) (m : ℕ) (omega delta a : ℝ)
    (J4 : Finset (Label4 m)) (cap4 : Label4 m → ℚ)
    (J5 : Finset (Label5 m)) (cap5 : Label5 m → ℚ) (N cap : ℕ) : ℝ :=
  ∑ j ∈ selectedFifthCells e chi m omega J5,
    signedShellCell e chi m omega delta a J4 cap4 cap5 N cap j

/-- Strict original prime order collapses every small face to t5<a;
the source and the actual own-cube difference are otherwise unchanged. -/
theorem smallCellRemainder_eq_terminal
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega a : ℝ)
    (J4 : Finset (Label4 m)) (cap4 : Label4 m → ℚ)
    (J5 : Finset (Label5 m)) (cap5 : Label5 m → ℚ)
    (N cap : ℕ) (hN : 1<N) (hcap : (N:ℝ)^(19/96:ℝ)≤(cap:ℝ)) (j : Label5 m) :
    P1OriginalFifthLimit.smallCellRemainder e chi m omega a J4 cap4 J5 cap5 N cap j =
      terminalCellRemainder e chi m omega a J4 cap4 cap5 N cap j := by
  unfold P1OriginalFifthLimit.smallCellRemainder terminalCellRemainder
  simp only [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases ht : actualPrimeTupleLog N p∈logPrimeMeshCell 0 (19/96) m j
  · have hc : p∈candidates (e:ℝ) chi m omega N cap := by
      simpa only [sourceCarrier,candidates] using hp
    have hd := (mem_candidates_iff_log_on_cell (e:ℝ) chi m omega
      N cap hN hcap p j ht).mp hc
    have hanti := ((mem_jointRegion (e:ℝ) chi m omega j _).mp hd.2).2.1
    have hface : (∃ i,actualPrimeTupleLog N p i<a) ↔ actualPrimeTupleLog N p 4<a := by
      constructor
      · exact P1OriginalFifthAllFacesAnalyticTail.last_lt_of_any_coordinate_lt _ hanti
      · intro hh
        exact ⟨4,hh⟩
    simp only [ht,if_true,hface,cellDifference]
  · simp only [ht,if_false,mul_zero,ite_self]

/-- Exact shell identity at a single genuine selected-mesh owner. -/
theorem smallCellRemainder_split
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega delta a : ℝ) (hda : delta≤a)
    (J4 : Finset (Label4 m)) (cap4 : Label4 m → ℚ)
    (J5 : Finset (Label5 m)) (cap5 : Label5 m → ℚ)
    (N cap : ℕ) (hN : 1<N) (hcap : (N:ℝ)^(19/96:ℝ)≤(cap:ℝ)) (j : Label5 m) :
    P1OriginalFifthLimit.smallCellRemainder e chi m omega a J4 cap4 J5 cap5 N cap j =
      P1OriginalFifthLimit.smallCellRemainder e chi m omega delta J4 cap4 J5 cap5 N cap j +
        signedShellCell e chi m omega delta a J4 cap4 cap5 N cap j := by
  rw [smallCellRemainder_eq_terminal e chi m omega a J4 cap4 J5 cap5 N cap hN hcap j,
    smallCellRemainder_eq_terminal e chi m omega delta J4 cap4 J5 cap5 N cap hN hcap j]
  unfold terminalCellRemainder signedShellCell shellCell
  simp only [Finset.sum_filter]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p _
  by_cases ht : actualPrimeTupleLog N p∈logPrimeMeshCell 0 (19/96) m j
  · by_cases hd : actualPrimeTupleLog N p 4<delta
    · have ha : actualPrimeTupleLog N p 4<a := hd.trans_le hda
      have hnd : ¬delta≤actualPrimeTupleLog N p 4 := not_le_of_gt hd
      simp [ht,hd,ha,hnd]
    · have hdl : delta≤actualPrimeTupleLog N p 4 := le_of_not_gt hd
      by_cases ha : actualPrimeTupleLog N p 4<a <;> simp [ht,hd,hdl,ha]
  · simp [ht]

/-- Exact finite splitting of the original coarse total remainder. -/
theorem smallRemainder_split
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega delta a : ℝ) (hda : delta≤a)
    (J4 : Finset (Label4 m)) (cap4 : Label4 m → ℚ)
    (J5 : Finset (Label5 m)) (cap5 : Label5 m → ℚ)
    (N cap : ℕ) (hN : 1<N) (hcap : (N:ℝ)^(19/96:ℝ)≤(cap:ℝ)) :
    P1OriginalFifthLimit.smallRemainder e chi m omega a J4 cap4 J5 cap5 N cap =
      P1OriginalFifthLimit.smallRemainder e chi m omega delta J4 cap4 J5 cap5 N cap +
        signedShell e chi m omega delta a J4 cap4 J5 cap5 N cap := by
  unfold P1OriginalFifthLimit.smallRemainder signedShell
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  exact smallCellRemainder_split e chi m omega delta a hda J4 cap4 J5 cap5 N cap hN hcap j

/-- The finite triangle inequality keeps the actual signed original
difference. The pointwise hypothesis concerns one tuple, never a sum. -/
theorem normalized_signedShellCell_le_quadraticMoment
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega delta a : ℝ) (ha : 0<a)
    (J4 : Finset (Label4 m)) (cap4 : Label4 m → ℚ)
    (J5 : Finset (Label5 m)) (cap5 : Label5 m → ℚ)
    (N cap : ℕ) (hN : 1<N) (hcap : (N:ℝ)^(19/96:ℝ)≤(cap:ℝ))
    (j : Label5 m) (hj : j∈selectedFifthCells e chi m omega J5)
    (q C : ℝ)
    (hpoint : ∀ p∈shellCell e chi m omega delta a N cap j,
      |cellDifference e chi m omega J4 cap4 cap5 N cap j p*q| ≤
        C*(actualPrimeTupleLog N p 4)^2) :
    |signedShellCell e chi m omega delta a J4 cap4 cap5 N cap j*q| ≤
      C*shellMoment e chi m omega delta a N cap j := by
  unfold signedShellCell shellMoment
  rw [Finset.sum_mul,Finset.mul_sum]
  calc
    _ ≤ ∑ p∈shellCell e chi m omega delta a N cap j,
        |((∏ i,1/((p i:ℝ)-1))*cellDifference e chi m omega J4 cap4 cap5 N cap j p)*q| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro p hp
      let r := owner a N p
      have hpbin : p∈shellBin e chi m omega delta a N cap j r :=
        Finset.mem_filter.mpr ⟨hp,rfl⟩
      have hw := actualPrimeBoxWeight_nonneg
        (shellBin_subset_prime_box e chi m omega delta a ha J5 N cap hN hcap j hj r hpbin)
      rw [mul_assoc,abs_mul,abs_of_nonneg hw]
      have hh := mul_le_mul_of_nonneg_left (hpoint p hp) hw
      convert hh using 1 <;> ring

/-- The same finite transport for every selected original label, retaining
the selected-cell multiplicity instead of assuming a disjoint mesh. -/
theorem normalized_signedShell_le_sum_quadraticMoments
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega delta a : ℝ) (ha : 0<a)
    (J4 : Finset (Label4 m)) (cap4 : Label4 m → ℚ)
    (J5 : Finset (Label5 m)) (cap5 : Label5 m → ℚ)
    (N cap : ℕ) (hN : 1<N) (hcap : (N:ℝ)^(19/96:ℝ)≤(cap:ℝ))
    (q C : ℝ)
    (hpoint : ∀ j∈selectedFifthCells e chi m omega J5,
      ∀ p∈shellCell e chi m omega delta a N cap j,
      |cellDifference e chi m omega J4 cap4 cap5 N cap j p*q| ≤
        C*(actualPrimeTupleLog N p 4)^2) :
    |signedShell e chi m omega delta a J4 cap4 J5 cap5 N cap*q| ≤
      C*∑ j∈selectedFifthCells e chi m omega J5,
        shellMoment e chi m omega delta a N cap j := by
  unfold signedShell
  rw [Finset.sum_mul,Finset.mul_sum]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro j hj
  exact normalized_signedShellCell_le_quadraticMoment e chi m omega delta a ha
    J4 cap4 J5 cap5 N cap hN hcap j hj q C (hpoint j hj)

end
end ImbalancedChen.P1OriginalFifthMiddleShellRemainderSplit
