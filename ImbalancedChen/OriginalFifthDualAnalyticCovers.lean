import ImbalancedChen.OriginalFifthNativeAtomChoices

/-!
SOURCE_ONLY / UNCOMPILED / ZERO_FORMAL_CREDIT.

Two constant ANALYTIC covering exponents are constructed before N from
the actual primitive atom's native old/new raw labels and an arbitrary
reference corner. Each stays between its own actual exponent+e/2 and
its own actual exponent+e. Thus the remaining e buffer lies below the
literal unbuffered tent (also for the selected Gamma seed).

The physical old/new policy exponents, own-cube decisions and signed
density are NOT changed to these constants. The corner need not belong
to the atom; the exact native labelled candidate extension is used there.
The 15/2 coordinate modulus counts all five possible selected slots.
-/

namespace ImbalancedChen.OriginalFifthDualAnalyticCovers20261026b

noncomputable section
open scoped Classical BigOperators
open Set VariableEnvelope
open P2OriginalFourthCapProducerInterface
open P1OriginalPrefixRowDecodeSoundness
open P1OriginalFullTableActualProducerAdapter
open P1OriginalVariableFourthContinuation
open P1OriginalVariableFifthContinuation
open P1ActualVariableFifthProfiles
open P1ActualVariableFourthFifthCellTestLimit
open OriginalFifthInheritedParentGeometry20261026b
open OriginalFifthRawPositionalJointOwnership20261026b
open OriginalFifthLiteralAffineSignBank20261026b
open OriginalFifthNativeAtomChoices20261026b

/-- Native scalar tent modulus and the actual selected-slot cardinality. -/
theorem selected_tent_oscillation {n : ℕ} (I : Finset (Fin n)) (hcard : I.card ≤ 5)
    (t u : Fin n → ℝ) (delta : ℝ) (hd : 0 ≤ delta)
    (hc : ∀ i, |t i - u i| ≤ delta) :
    |v (∑ i ∈ I, t i) - v (∑ i ∈ I, u i)| ≤ (15 / 2 : ℝ) * delta := by
  have hs : |(∑ i ∈ I, t i) - ∑ i ∈ I, u i| ≤ (I.card : ℝ) * delta := by
    rw [← Finset.sum_sub_distrib]
    calc
      |∑ i ∈ I, (t i - u i)| ≤ ∑ i ∈ I, |t i - u i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ I, delta := Finset.sum_le_sum (fun i _ => hc i)
      _ = (I.card : ℝ) * delta := by simp [nsmul_eq_mul]
  have hcr : (I.card : ℝ) ≤ 5 := by exact_mod_cast hcard
  have hs5 := hs.trans (mul_le_mul_of_nonneg_right hcr hd)
  have hv := v_abs_sub_le_of_le hs5
  nlinarith

theorem native_parent_oscillation
    (R4 : List FourthWireRow) (e : ℚ) (m : ℕ) (j : Fin 5 → Fin (m + 1))
    (p : ParentPosition R4) (t u : Fin 5 → ℝ) (delta : ℝ) (hd : 0 ≤ delta)
    (hc : ∀ i, |t i - u i| ≤ delta) :
    |parentValue R4 e m j p t - parentValue R4 e m j p u| ≤ (15 / 2 : ℝ) * delta := by
  refine Fin.cases ?_ (fun k => ?_) p
  · change |selectedSeed e m j - selectedSeed e m j| ≤ _
    simp only [sub_self, abs_zero]
    positivity
  · let row := OriginalFullFourthPriorityOwnership20261026a.rowAt R4 k
    have hcard : row.selected.card ≤ 5 :=
      (Finset.card_le_univ row.selected).trans (by decide : Fintype.card (Fin 4) ≤ 5)
    have hf : ∀ i : Fin 4, |firstFour t i - firstFour u i| ≤ delta := by
      intro i
      exact hc (i.castLE (by decide : 4 ≤ 5))
    have h := selected_tent_oscillation row.selected hcard (firstFour t) (firstFour u) delta hd hf
    change |row.bufferedCandidate (e : ℝ) (firstFour t) -
      row.bufferedCandidate (e : ℝ) (firstFour u)| ≤ _
    rw [ProducerRow.bufferedCandidate_eq, ProducerRow.bufferedCandidate_eq]
    have heq : (v (∑ i ∈ row.selected, firstFour t i) - 2 * (e : ℝ)) -
        (v (∑ i ∈ row.selected, firstFour u i) - 2 * (e : ℝ)) =
        v (∑ i ∈ row.selected, firstFour t i) - v (∑ i ∈ row.selected, firstFour u i) := by ring
    rw [heq]
    exact h

theorem native_fifth_candidate_oscillation (e : ℚ) (I : Finset (Fin 5))
    (t u : Fin 5 → ℝ) (delta : ℝ) (hd : 0 ≤ delta)
    (hc : ∀ i, |t i - u i| ≤ delta) :
    |candidate (e : ℝ) I t - candidate (e : ℝ) I u| ≤ (15 / 2 : ℝ) * delta := by
  have h := selected_tent_oscillation I (by simpa using Finset.card_le_univ I) t u delta hd hc
  unfold candidate
  rw [envelope_eq_v, envelope_eq_v]
  have heq : (v (∑ i ∈ I, t i) - 2 * (e : ℝ)) - (v (∑ i ∈ I, u i) - 2 * (e : ℝ)) =
      v (∑ i ∈ I, t i) - v (∑ i ∈ I, u i) := by ring
  rw [heq]
  exact h

theorem native_successor_oscillation
    (R4 : List FourthWireRow) (R5 : List FifthWireRow) (e : ℚ) (m : ℕ)
    (j : Fin 5 → Fin (m + 1)) (p : JointPosition R4 R5) (t u : Fin 5 → ℝ)
    (delta : ℝ) (hd : 0 ≤ delta) (hc : ∀ i, |t i - u i| ≤ delta) :
    |slotValue R4 R5 e m j p.1 t p.2 - slotValue R4 R5 e m j p.1 u p.2| ≤
      (15 / 2 : ℝ) * delta := by
  refine Fin.cases ?_ (fun k => ?_) p.2
  · exact native_parent_oscillation R4 e m j p.1 t u delta hd hc
  · exact native_fifth_candidate_oscillation e (rawRowAt R5 m j k).selected t u delta hd hc

/-- First component covers OLD, second covers NEW, each from its own
native extension at the same corner. No maximum between these is used. -/
def dualCovers (R4 : List FourthWireRow) (R5 : List FifthWireRow) (e : ℚ) (m : ℕ)
    (j : Fin 5 → Fin (m + 1)) (p : JointPosition R4 R5) (corner : Fin 5 → ℝ) (delta : ℝ) : ℝ × ℝ :=
  (parentValue R4 e m j p.1 corner + (15 / 2 : ℝ) * delta + (e : ℝ) / 2,
    slotValue R4 R5 e m j p.1 corner p.2 + (15 / 2 : ℝ) * delta + (e : ℝ) / 2)

theorem dualCovers_brackets
    (R4 : List FourthWireRow) (R5 : List FifthWireRow) (e : ℚ) (m : ℕ)
    (j : Fin 5 → Fin (m + 1)) (p : JointPosition R4 R5) (corner t : Fin 5 → ℝ)
    (delta : ℝ) (hd : 0 ≤ delta) (hsmall : delta ≤ (e : ℝ) / 30)
    (hc : ∀ i, |t i - corner i| ≤ delta) :
    (parentValue R4 e m j p.1 t + (e : ℝ) / 2 ≤ (dualCovers R4 R5 e m j p corner delta).1 ∧
      (dualCovers R4 R5 e m j p corner delta).1 ≤ parentValue R4 e m j p.1 t + (e : ℝ)) ∧
    (slotValue R4 R5 e m j p.1 t p.2 + (e : ℝ) / 2 ≤ (dualCovers R4 R5 e m j p corner delta).2 ∧
      (dualCovers R4 R5 e m j p corner delta).2 ≤ slotValue R4 R5 e m j p.1 t p.2 + (e : ℝ)) := by
  have hOld := abs_le.mp (native_parent_oscillation R4 e m j p.1 t corner delta hd hc)
  have hNew := abs_le.mp (native_successor_oscillation R4 R5 e m j p t corner delta hd hc)
  unfold dualCovers
  constructor <;> constructor <;> nlinarith

/-- Both literal unbuffered candidate extensions retain an entire e
reserve above the two constant analytic covers. The seed's extension is
Gamma = selectedSeed+2e, so the same exact identity includes that branch. -/
theorem dualCovers_below_unbuffered
    (R4 : List FourthWireRow) (R5 : List FifthWireRow) (e : ℚ) (m : ℕ)
    (j : Fin 5 → Fin (m + 1)) (p : JointPosition R4 R5) (corner t : Fin 5 → ℝ)
    (delta : ℝ) (hd : 0 ≤ delta) (hsmall : delta ≤ (e : ℝ) / 30)
    (hc : ∀ i, |t i - corner i| ≤ delta) :
    (dualCovers R4 R5 e m j p corner delta).1 + (e : ℝ) ≤ parentValue R4 e m j p.1 t + 2 * (e : ℝ) ∧
      (dualCovers R4 R5 e m j p corner delta).2 + (e : ℝ) ≤ slotValue R4 R5 e m j p.1 t p.2 + 2 * (e : ℝ) := by
  have h := dualCovers_brackets R4 R5 e m j p corner t delta hd hsmall hc
  constructor <;> linarith [h.1.2, h.2.2]

/-- On an occupied ORIGINAL primitive atom the actual OLD and NEW cap
each receive their own constant cover, without replacing either density. -/
theorem actual_atom_dualCovers
    (R4 : List FourthWireRow) (R5 : List FifthWireRow) (e : ℚ) (chi : ℝ)
    (m : ℕ) (omega : ℝ) (J : Finset (Fin 5 → Fin (m + 1))) (j : Fin 5 → Fin (m + 1))
    (hj : j ∈ P1OriginalCoarseFifthContinuation.selectedFifthCells e chi m omega J)
    (L : ProducerRow → Prop) (w : SignWord R4 R5) (hw : (signAtom R4 R5 e m j w).Nonempty)
    (corner t : Fin 5 → ℝ) (delta : ℝ) (hd : 0 ≤ delta) (hsmall : delta ≤ (e : ℝ) / 30)
    (ht : t ∈ signAtom R4 R5 e m j w) (hm : t ∈ logPrimeMeshCell 0 (19 / 96) m j)
    (hc : ∀ i, |t i - corner i| ≤ delta) :
    let C := dualCovers R4 R5 e m j (atomChoice R4 R5 e m j L w hw) corner delta
    (originalVariableFourthProfile e chi omega m j (fourthFamily R4) L t + (e : ℝ) / 2 ≤ C.1 ∧
      C.1 ≤ originalVariableFourthProfile e chi omega m j (fourthFamily R4) L t + (e : ℝ)) ∧
    (actualNext5 e chi m omega j (fourthFamily R4) L (fifthFamily R5 m) t + (e : ℝ) / 2 ≤ C.2 ∧
      C.2 ≤ actualNext5 e chi m omega j (fourthFamily R4) L (fifthFamily R5 m) t + (e : ℝ)) := by
  dsimp only
  have hcaps := actual_caps_from_atomChoice R4 R5 e chi m omega J j hj L w hw ht hm
  rw [hcaps.1, hcaps.2]
  exact dualCovers_brackets R4 R5 e m j _ corner t delta hd hsmall hc

end
end ImbalancedChen.OriginalFifthDualAnalyticCovers20261026b
