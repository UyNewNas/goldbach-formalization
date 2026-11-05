import ImbalancedChen.P4AOriginalFull87EighthPrimeMeanLedger

/-!
SOURCE ONLY / UNCOMPILED / UNEVALUATED.

Charge the arithmetic error only on the actual rank-eight occurrence states
whose own-sixth parent level differs from the existing saved eighth cap.
The original owner, strict trim, signed first-exit continuation, whole
modulus, remaining rough carrier and per-leaf beta are unchanged.

This is a finite, one-rho identity and bound. No exit-series asymptotic,
primitive-discrepancy estimate, or reserve payment is claimed.
-/
namespace ImbalancedChen.P4AOriginalFull87ChangedFrontierBudget
noncomputable section
open scoped Classical BigOperators
open P1Pair12RetainedSignedSource
open P4AOriginalFull87SourceDictionary (Cell)
open P4AOriginalFull87FiniteEighthCap (finiteCap)
open P4AOriginalFull87SourceDispatch (point8)
open P4AOriginalFull87EighthKernelIntegration (actualParent)
open P4AOriginalFull87OwnedEighthSource
open P4AOriginalFull87EighthPrimeMeanLedger

/-- A finite list may be restricted to the positions at which its summand
is nonzero. Unlike a Finset reindexing this preserves occurrence repeats. -/
theorem sum_map_filter_of_zero {α : Type*} (xs : List α) (f : α → ℝ)
    (keep : α → Bool)
    (hz : ∀ x ∈ xs, keep x = false → f x = 0) :
    (xs.map f).sum = ((xs.filter keep).map f).sum := by
  revert hz
  induction xs with
  | nil => intro _; simp
  | cons x xs ih =>
      intro hz
      have htail : ∀ y ∈ xs, keep y = false → f y = 0 := by
        intro y hy
        exact hz y (List.mem_cons_of_mem x hy)
      have hrec := ih htail
      by_cases hx : keep x = true
      · simp only [List.map_cons, List.sum_cons]
        simpa [List.filter_cons, hx] using congrArg (fun v : ℝ => f x + v) hrec
      · have hf : keep x = false := by cases hb : keep x <;> simp_all
        have hzero : f x = 0 := hz x (by simp) hf
        simp only [List.map_cons, List.sum_cons]
        simp [List.filter_cons, hf, hzero, hrec]

/-- The ordinary saving is exactly zero if the two real levels coincide;
there is no cap-monotonicity argument for signed coefficients here. -/
theorem ordinarySaving_zero_of_equal
    (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w L : ℝ) (G : ℕ → ℝ) (c : Cell)
    (s : FirstExitDepthState ℕ)
    (heq : actualParent n e q om (N : ℝ) s.selectedPrefix =
      (finiteCap n c (point8 (N : ℝ) s.selectedPrefix) : ℝ)) :
    ordinarySaving n e q om N cap w L G c s = 0 := by
  unfold ordinarySaving
  rw [heq, sub_self]

/-- This is a FILTER of the existing owner occurrence list, not a new
selector, region, admission predicate, or rebuilt frontier. -/
def changedStates (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ)
    (om : ℝ) (N cap : ℕ) (w z : ℝ) (c : Cell) :
    List (FirstExitDepthState ℕ) :=
  (P4AOriginalFull87LicensedSixthRealization.states
      delta n e q om N cap w z (fun _ => 1) c).filter
    (fun s => decide (actualParent n e q om (N : ℝ) s.selectedPrefix ≠
      (finiteCap n c (point8 (N : ℝ) s.selectedPrefix) : ℝ)))

/-- Every retained source occurrence with equal old/new caps vanishes.
No boundary or zero-measure argument is used to remove it. -/
theorem ownedSource_eq_changed
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (G : ℕ → ℝ) (c : Cell) :
    ownedSource delta n e q om N cap w z L G c =
      ((changedStates delta n e q om N cap w z c).map
        (ordinarySaving n e q om N cap w L G c)).sum := by
  unfold ownedSource changedStates
  apply sum_map_filter_of_zero
  intro s _ hfalse
  by_cases hc : actualParent n e q om (N : ℝ) s.selectedPrefix =
      (finiteCap n c (point8 (N : ℝ) s.selectedPrefix) : ℝ)
  · exact ordinarySaving_zero_of_equal n e q om N cap w L G c s hc
  · simp [hc] at hfalse

/-- Exact change of the SAME signed physical coefficient, now supported
only at the actual changed eighth occurrences with original multiplicity. -/
theorem gain_eq_changed_sources
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (G : ℕ → ℝ) :
    gain delta n e q om N cap w z L G =
      ∑ c : Cell, ((changedStates delta n e q om N cap w z c).map
        (ordinarySaving n e q om N cap w L G c)).sum := by
  rw [gain_eq_owned_sources]
  apply Finset.sum_congr rfl
  intro c _
  exact ownedSource_eq_changed delta n e q om N cap w z L G c

/-- Elementary triangle inequality for occurrence lists. -/
theorem abs_list_sum_le (xs : List ℝ) :
    |xs.sum| ≤ (xs.map abs).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.sum_cons, List.map_cons]
      exact (abs_add_le x xs.sum).trans (add_le_add_left ih |x|)

/-- The actual changed-source absolute budget. It retains the *signed
ordinary-saving difference* inside the absolute value, not the total
absolute rho of both complete trees. -/
def changedAbsBudget
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (G : ℕ → ℝ) : ℝ :=
  ∑ c : Cell, ((changedStates delta n e q om N cap w z c).map
    (fun s => |ordinarySaving n e q om N cap w L G c s|)).sum

theorem changedAbsBudget_nonneg
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (G : ℕ → ℝ) :
    0 ≤ changedAbsBudget delta n e q om N cap w z L G := by
  unfold changedAbsBudget
  apply Finset.sum_nonneg
  intro c _
  induction changedStates delta n e q om N cap w z c with
  | nil => simp
  | cons s xs ih =>
      simp only [List.map_cons, List.sum_cons]
      exact add_nonneg (abs_nonneg _) ih

/-- All arithmetic error is charged only where the eighth update
actually changes its inherited real sieve level. -/
theorem abs_gain_le_changed_budget
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (G : ℕ → ℝ) :
    |gain delta n e q om N cap w z L G| ≤
      changedAbsBudget delta n e q om N cap w z L G := by
  rw [gain_eq_changed_sources]
  unfold changedAbsBudget
  calc
    |∑ c : Cell, ((changedStates delta n e q om N cap w z c).map
        (ordinarySaving n e q om N cap w L G c)).sum|
      ≤ ∑ c : Cell, |((changedStates delta n e q om N cap w z c).map
          (ordinarySaving n e q om N cap w L G c)).sum| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ c : Cell, ((changedStates delta n e q om N cap w z c).map
          (fun s => |ordinarySaving n e q om N cap w L G c s|)).sum := by
        apply Finset.sum_le_sum
        intro c _
        simpa only [List.map_map] using
          abs_list_sum_le ((changedStates delta n e q om N cap w z c).map
            (ordinarySaving n e q om N cap w L G c))

/-- The exact single full-modulus residual, including both exceptional
prime populations with their signs. No distribution conclusion is assumed. -/
def arithmeticResidual (N d : ℕ) : ℝ :=
  primitiveError N d - modulusPrimeTerm N d - chenCentrePrimeAPCount N N d

theorem receiverTest_eq_density_add_residual (N d : ℕ) :
    receiverTest N d = primeMass N * densityTest d + arithmeticResidual N d := by
  unfold arithmeticResidual primitiveError
  rw [exactCoprimeMean_eq_density_sub_modulus, receiverTest_eq]
  ring

theorem receiver_gain_eq_density_add_residual
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) :
    gain delta n e q om N cap w z L (receiverTest N) =
      primeMass N * gain delta n e q om N cap w z L densityTest +
      gain delta n e q om N cap w z L (arithmeticResidual N) := by
  have hfun : receiverTest N =
      fun d => primeMass N * densityTest d + arithmeticResidual N d := by
    funext d
    exact receiverTest_eq_density_add_residual N d
  rw [hfun]
  simpa only [one_mul] using
    gain_linear delta n e q om N cap w z L densityTest (arithmeticResidual N)
      (primeMass N) 1

/-- One shared *changed-frontier* payment for the signed sum of all three
arithmetic defects. This does not take three separate absolute values
before the common signed ordinary continuation has been evaluated. -/
theorem receiver_density_changed_error_bound
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) :
    |gain delta n e q om N cap w z L (receiverTest N) -
      primeMass N * gain delta n e q om N cap w z L densityTest| ≤
      changedAbsBudget delta n e q om N cap w z L (arithmeticResidual N) := by
  rw [receiver_gain_eq_density_add_residual]
  simp only [add_sub_cancel_left]
  exact abs_gain_le_changed_budget delta n e q om N cap w z L (arithmeticResidual N)

/-- The one-sided form is the actual reserve-facing finite inequality.
It makes no assertion that the RHS is o(primeMass * normalization). -/
theorem receiver_density_changed_lower
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) :
    primeMass N * gain delta n e q om N cap w z L densityTest -
      changedAbsBudget delta n e q om N cap w z L (arithmeticResidual N) ≤
      gain delta n e q om N cap w z L (receiverTest N) := by
  have h := receiver_density_changed_error_bound delta n e q om N cap w z L
  have hl := (abs_le.mp h).1
  linarith


/-- Alternative P3-facing payment: if the three defects are estimated
separately, the triangle inequality is applied to their actual changed
ordinary continuations, never to the unchanged physical tree masses. -/
theorem receiver_density_three_changed_error_bound
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) :
    |gain delta n e q om N cap w z L (receiverTest N) -
      primeMass N * gain delta n e q om N cap w z L densityTest| ≤
      changedAbsBudget delta n e q om N cap w z L (primitiveError N) +
      changedAbsBudget delta n e q om N cap w z L (modulusPrimeTerm N) +
      changedAbsBudget delta n e q om N cap w z L (chenCentrePrimeAPCount N N) := by
  let A := gain delta n e q om N cap w z L (primitiveError N)
  let B := gain delta n e q om N cap w z L (modulusPrimeTerm N)
  let C := gain delta n e q om N cap w z L (chenCentrePrimeAPCount N N)
  have hdecomp :
      gain delta n e q om N cap w z L (receiverTest N) -
        primeMass N * gain delta n e q om N cap w z L densityTest = A - B - C := by
    dsimp only [A, B, C]
    rw [receiver_gain_decomposition]
    ring
  rw [hdecomp]
  have h1 : |A - B| ≤ |A| + |B| := by
    simpa only [sub_eq_add_neg, abs_neg] using abs_add A (-B)
  have h2 : |A - B - C| ≤ |A - B| + |C| := by
    simpa only [sub_eq_add_neg, abs_neg] using abs_add (A - B) (-C)
  have hA : |A| ≤ changedAbsBudget delta n e q om N cap w z L (primitiveError N) :=
    abs_gain_le_changed_budget delta n e q om N cap w z L (primitiveError N)
  have hB : |B| ≤ changedAbsBudget delta n e q om N cap w z L (modulusPrimeTerm N) :=
    abs_gain_le_changed_budget delta n e q om N cap w z L (modulusPrimeTerm N)
  have hC : |C| ≤ changedAbsBudget delta n e q om N cap w z L
      (chenCentrePrimeAPCount N N) :=
    abs_gain_le_changed_budget delta n e q om N cap w z L (chenCentrePrimeAPCount N N)
  linarith

end
end ImbalancedChen.P4AOriginalFull87ChangedFrontierBudget
