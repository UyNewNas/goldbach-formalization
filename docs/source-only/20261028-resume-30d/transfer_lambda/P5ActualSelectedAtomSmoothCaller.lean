import ImbalancedChen.P5NativeSelectedFourIntegerProfile
import ImbalancedChen.P5IndependentSmoothWPhysicalChartInterface

/-!
SOURCE ONLY / UNCOMPILED_ZERO_CREDIT.
The sharp selected atom below is defined from the ORIGINAL region and
owned cell, independently of the smooth candidate. Its signed PP caller
is related to the smooth caller by an exact ORIGINAL-wall remainder.
No equality of a sharp indicator and a smooth function is asserted.
-/
namespace ImbalancedChen.P5Z.ActualSelectedAtomSmoothCaller

noncomputable section
open Classical Set
open scoped BigOperators
open U11Integral U1011OriginalFifteenNativeGridCells
open U1011OriginalSixteenArithmeticProducts
open U1011OriginalMaskSmoothBoxRealization
open U1011OriginalPairedFixedMaskHarmonic
open NativeSelectedFourIntegerProfile
open ActualFourSmoothProfileEvaluation
open IndependentSmoothCoverProductEnvelope
open IndependentSmoothWPhysicalChartInterface
open OriginalOrdinaryPresievedSigma OriginalJointPresievedCompiler
open ActualJointSigmaSortedChartAttachment

-- This is the independently defined original selected atom: same E,
-- same original state, same Ico native owner. No smooth candidate occurs.
def selectedAtom (D : Data) : Set LogFour :=
  cube ∩ (originalCell (outerUnion D.rows) D.state ∩ cell D.ownerMesh D.owner)

def sharpSelectedWeight (D : Data) (N : ℕ)
    (u : Fin 4 → Fin (N+1)) : ℝ :=
  if actualPrimeTupleLog N (fun i => (u i).val) ∈ selectedAtom D then 1 else 0

def differenceWeight (D : Data) (lowerSide : Bool) (N : ℕ)
    (u : Fin 4 → Fin (N+1)) : ℝ :=
  sharpSelectedWeight D N u - primeWeight D lowerSide N u

-- The outside-cube term records the true smooth collar. It is not the
-- whole complement of the cube: every coordinate stays within width of
-- its fixed original box and at least one original cube face is crossed.
def wallReserve (D : Data) (lowerSide : Bool) (v : LogFour) : Prop :=
  originalReserve lowerSide D.rows D.state D.ownerMesh D.owner
      D.smoothMesh D.width v ∨
    (v ∉ cube ∧ ∀ i, (lower : ℝ)-D.width < v i ∧ v i < (upper : ℝ)+D.width)

theorem sharp_eq_original_indicator_on_cube (D : Data) (N : ℕ)
    (u : Fin 4 → Fin (N+1))
    (hv : actualPrimeTupleLog N (fun i => (u i).val) ∈ cube) :
    sharpSelectedWeight D N u =
      retainedIndicator D.rows D.state D.ownerMesh D.owner
        (actualPrimeTupleLog N (fun i => (u i).val)) := by
  simp only [sharpSelectedWeight, selectedAtom, Set.mem_inter_iff,
    retainedIndicator, hv, true_and]

theorem primeWeight_eq_native_log_cover (D : Data) (lowerSide : Bool)
    {N : ℕ} (hN : 2 ≤ N) (u : Fin 4 → Fin (N+1))
    (hu : u ∈ Part3.labelledPrimeTuples 4 N) :
    primeWeight D lowerSide N u =
      signedSmoothCover lowerSide D.rows D.state D.ownerMesh D.owner
        D.smoothMesh D.width (actualPrimeTupleLog N (fun i => (u i).val)) :=
  exact_native_prime_evaluation D lowerSide hN u hu

theorem difference_supported_on_actual_walls (D : Data) (lowerSide : Bool)
    {N : ℕ} (hN : 2 ≤ N) (u : Fin 4 → Fin (N+1))
    (hu : u ∈ Part3.labelledPrimeTuples 4 N)
    (hdiff : differenceWeight D lowerSide N u ≠ 0) :
    wallReserve D lowerSide (actualPrimeTupleLog N (fun i => (u i).val)) := by
  let v := actualPrimeTupleLog N (fun i => (u i).val)
  have hprofile := primeWeight_eq_native_log_cover D lowerSide hN u hu
  by_cases hv : v ∈ cube
  · apply Or.inl
    apply original_mask_error_supported lowerSide D.rows D.state D.ownerMesh
      D.owner D.smoothMesh D.width_pos hv
    intro hz
    have heq : signedSmoothCover lowerSide D.rows D.state D.ownerMesh D.owner
        D.smoothMesh D.width v =
      retainedIndicator D.rows D.state D.ownerMesh D.owner v := sub_eq_zero.mp hz
    apply hdiff
    unfold differenceWeight
    rw [sharp_eq_original_indicator_on_cube D N u hv, hprofile]
    exact sub_eq_zero.mpr heq.symm
  · apply Or.inr
    refine ⟨hv, ?_⟩
    have hsharp : sharpSelectedWeight D N u = 0 := by
      change (if v ∈ selectedAtom D then (1 : ℝ) else 0) = 0
      simp only [selectedAtom, Set.mem_inter_iff]
      exact if_neg (fun h => hv h.1)
    have hnonzero : signedSmoothCover lowerSide D.rows D.state D.ownerMesh D.owner
        D.smoothMesh D.width v ≠ 0 := by
      intro hz
      apply hdiff
      unfold differenceWeight
      rw [hsharp, hprofile, hz]
      exact sub_self _
    exact signedSmoothCover_nonzero_collar D.width_pos lowerSide D.rows D.state
      D.ownerMesh D.owner D.smoothMesh v hnonzero

theorem sharp_amplitude (D : Data) (N : ℕ) (u : Fin 4 → Fin (N+1)) :
    |sharpSelectedWeight D N u| ≤ 1 := by
  unfold sharpSelectedWeight
  split_ifs <;> norm_num

-- The original count-minus-exact-coprime-mean kernel and its absolute
-- payment are both literal. q=0 is totalized by the same /phi(0)=0.
def ppKernel (N q : ℕ) (u : Fin 4 → Fin (N+1)) : ℝ :=
  (if Nat.ModEq q (Part3.labelledProduct u) N then 1 else 0) -
    (if Nat.Coprime (Part3.labelledProduct u) q then 1 else 0) / (Nat.totient q : ℝ)

def positivePaymentKernel (N q : ℕ) (u : Fin 4 → Fin (N+1)) : ℝ :=
  (if Nat.ModEq q (Part3.labelledProduct u) N then 1 else 0) +
    (if Nat.Coprime (Part3.labelledProduct u) q then 1 else 0) / (Nat.totient q : ℝ)

theorem paymentKernel_nonneg (N q : ℕ) (u : Fin 4 → Fin (N+1)) :
    0 ≤ positivePaymentKernel N q u := by
  unfold positivePaymentKernel
  positivity

theorem kernel_abs_le_payment (N q : ℕ) (u : Fin 4 → Fin (N+1)) :
    |ppKernel N q u| ≤ positivePaymentKernel N q u := by
  have hc : (0 : ℝ) ≤
      (if Nat.ModEq q (Part3.labelledProduct u) N then (1 : ℝ) else 0) := by positivity
  have hm : (0 : ℝ) ≤
      (if Nat.Coprime (Part3.labelledProduct u) q then (1 : ℝ) else 0) /
        (Nat.totient q : ℝ) := by positivity
  simpa only [ppKernel, positivePaymentKernel, abs_of_nonneg hc,
    abs_of_nonneg hm] using abs_sub_le
      (if Nat.ModEq q (Part3.labelledProduct u) N then (1 : ℝ) else 0)
      ((if Nat.Coprime (Part3.labelledProduct u) q then (1 : ℝ) else 0) /
        (Nat.totient q : ℝ))

def reservePayment (D : Data) (lowerSide : Bool) (N : ℕ)
    (Q : Finset ℕ) (rho : ℕ → ℝ) : ℝ :=
  ∑ q ∈ Q, |rho q| *
    ∑ u ∈ Part3.labelledPrimeTuples 4 N,
      if wallReserve D lowerSide (actualPrimeTupleLog N (fun i => (u i).val))
      then positivePaymentKernel N q u else 0

theorem signedError_sub (N : ℕ) (Q : Finset ℕ) (rho : ℕ → ℝ)
    (W V : (Fin 4 → Fin (N+1)) → ℝ) :
    Part3.primeProductSignedError 4 N N Q rho (fun u => W u - V u) =
      Part3.primeProductSignedError 4 N N Q rho W -
        Part3.primeProductSignedError 4 N N Q rho V := by
  simp only [Part3.primeProductSignedError, sub_mul, Finset.sum_sub_distrib,
    mul_sub]

theorem actual_selected_caller_exact (D : Data) (lowerSide : Bool)
    (N : ℕ) (Q : Finset ℕ) (rho : ℕ → ℝ) :
    Part3.primeProductSignedError 4 N N Q rho (sharpSelectedWeight D N) =
      Part3.primeProductSignedError 4 N N Q rho (primeWeight D lowerSide N) +
        Part3.primeProductSignedError 4 N N Q rho (differenceWeight D lowerSide N) := by
  rw [show differenceWeight D lowerSide N =
      (fun u => sharpSelectedWeight D N u - primeWeight D lowerSide N u) from rfl,
    signedError_sub]
  ring

theorem actual_wall_payment_bound (D : Data) (lowerSide : Bool)
    {N : ℕ} (hN : 2 ≤ N) (Q : Finset ℕ) (rho : ℕ → ℝ)
    (C : ℝ) (hC : 0 ≤ C)
    (hamp : ∀ p : Fin 4 → ℝ, |profile D lowerSide N p| ≤ C) :
    |Part3.primeProductSignedError 4 N N Q rho (differenceWeight D lowerSide N)| ≤
      (1+C) * reservePayment D lowerSide N Q rho := by
  have hterm (q : ℕ) (u : Fin 4 → Fin (N+1))
      (hu : u ∈ Part3.labelledPrimeTuples 4 N) :
      |differenceWeight D lowerSide N u * ppKernel N q u| ≤
        (1+C) *
          (if wallReserve D lowerSide (actualPrimeTupleLog N (fun i => (u i).val))
            then positivePaymentKernel N q u else 0) := by
    by_cases hr : wallReserve D lowerSide
        (actualPrimeTupleLog N (fun i => (u i).val))
    · rw [if_pos hr, abs_mul]
      have hdiff : |differenceWeight D lowerSide N u| ≤ 1+C := by
        exact (abs_sub_le _ _).trans (add_le_add (sharp_amplitude D N u)
          (hamp (fun i => ((u i).val : ℝ))))
      exact mul_le_mul hdiff (kernel_abs_le_payment N q u)
        (abs_nonneg _) (by linarith)
    · have hz : differenceWeight D lowerSide N u = 0 := by
        by_contra h
        exact hr (difference_supported_on_actual_walls D lowerSide hN u hu h)
      simp only [hz, zero_mul, abs_zero, if_neg hr, mul_zero, le_refl]
  change |∑ q ∈ Q, rho q *
    ∑ u ∈ Part3.labelledPrimeTuples 4 N,
      differenceWeight D lowerSide N u * ppKernel N q u| ≤ _
  calc
    _ ≤ ∑ q ∈ Q, |rho q| *
        ∑ u ∈ Part3.labelledPrimeTuples 4 N,
          |differenceWeight D lowerSide N u * ppKernel N q u| := by
      apply (show |∑ q ∈ Q, rho q *
          ∑ u ∈ Part3.labelledPrimeTuples 4 N,
            differenceWeight D lowerSide N u * ppKernel N q u| ≤
        ∑ q ∈ Q, |rho q *
          ∑ u ∈ Part3.labelledPrimeTuples 4 N,
            differenceWeight D lowerSide N u * ppKernel N q u| from
          by simpa only [Real.norm_eq_abs] using norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro q hq
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left
        (by simpa only [Real.norm_eq_abs] using norm_sum_le
          (Part3.labelledPrimeTuples 4 N)
          (fun u => differenceWeight D lowerSide N u * ppKernel N q u)) (abs_nonneg _)
    _ ≤ ∑ q ∈ Q, |rho q| *
        ∑ u ∈ Part3.labelledPrimeTuples 4 N,
          (1+C) *
            (if wallReserve D lowerSide (actualPrimeTupleLog N (fun i => (u i).val))
              then positivePaymentKernel N q u else 0) := by
      apply Finset.sum_le_sum
      intro q hq
      exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun u hu => hterm q u hu))
        (abs_nonneg _)
    _ = _ := by
      simp only [← Finset.mul_sum, reservePayment]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q hq
      ring

-- Instantiating the exact difference at the ORIGINAL physical row sum
-- retains the same jointPresievedSigma, not a newly chosen positive rho.
theorem actual_rows_eq_signedError (n N : ℕ) (eta : ℚ) (w B : ℝ)
    (E : ℕ × ℕ → Prop) (W : (Fin 4 → Fin (N+1)) → ℝ) :
    actualSmoothSignedRows n N eta w B E W =
      Part3.primeProductSignedError 4 N N (jointSupport n N eta w E)
        (jointPresievedSigma n N eta w B E) W := by
  have hsorted := actual_joint_rows_eq_sorted_signed_error 4 N n N N eta w B E W
  have hpp := P5Z.LabelledPermutationWeightedSort.primeProductSignedError_eq_sorted_fibres
    4 N N (jointSupport n N eta w E) (jointPresievedSigma n N eta w B E) W
  simpa only [actualSmoothSignedRows] using hsorted.trans hpp.symm

theorem native_selected_actual_rows_exact (D : Data) (lowerSide : Bool)
    (n N : ℕ) (eta : ℚ) (w B : ℝ) (E : ℕ × ℕ → Prop) :
    actualSmoothSignedRows n N eta w B E (sharpSelectedWeight D N) =
      actualSmoothSignedRows n N eta w B E (primeWeight D lowerSide N) +
        Part3.primeProductSignedError 4 N N (jointSupport n N eta w E)
          (jointPresievedSigma n N eta w B E) (differenceWeight D lowerSide N) := by
  rw [actual_rows_eq_signedError, actual_rows_eq_signedError]
  exact actual_selected_caller_exact D lowerSide N
    (jointSupport n N eta w E) (jointPresievedSigma n N eta w B E)

theorem native_selected_actual_rows_wall_payment (D : Data) :
    ∃ C : ℕ, 0 < C ∧ ∀ (lowerSide : Bool) (n N : ℕ), 2 ≤ N →
      ∀ (eta : ℚ) (w B : ℝ) (E : ℕ × ℕ → Prop),
        |actualSmoothSignedRows n N eta w B E (sharpSelectedWeight D N) -
          actualSmoothSignedRows n N eta w B E (primeWeight D lowerSide N)| ≤
          (1+(C : ℝ)) * reservePayment D lowerSide N (jointSupport n N eta w E)
            (jointPresievedSigma n N eta w B E) := by
  obtain ⟨C, hC, hamp⟩ := native_uniform_integer_amplitude D
  refine ⟨C, hC, ?_⟩
  intro lowerSide n N hN eta w B E
  rw [native_selected_actual_rows_exact D lowerSide n N eta w B E, add_sub_cancel_left]
  exact actual_wall_payment_bound D lowerSide hN (jointSupport n N eta w E)
    (jointPresievedSigma n N eta w B E) C (Nat.cast_nonneg _) (hamp lowerSide N)

end
end ImbalancedChen.P5Z.ActualSelectedAtomSmoothCaller
