import ImbalancedChen.P3U5OriginalWComposition

/-!
P3.6 / manuscript-internal / SOURCE ONLY / UNCOMPILED / KERNEL-UNVERIFIED.
An arbitrary ORIGINAL labelled-prime weight W_T is evaluated on the full
original group products after HB, not on individual HB factors, a residual
quotient, a changed atom, or a modulus-dependent geometric filter.
The exact positive-scale logarithmic coordinates are reconstructed.

This file is algebra only. It makes no derivative-class or PP assertion.
-/
namespace ImbalancedChen.P3PhysicalOriginalW
noncomputable section
open scoped Classical BigOperators Topology
open P3AffineTransitionJets P3U5PhysicalProductChart P3HBLogSourceDictionary

/-- Each expanded HB slot occupies its original individual rectangle. -/
def slotValue {d : ℕ} (U : Fin d → ℝ) (z : Point d) : Fin d → ℝ :=
  fun i => U i * Real.exp (z i)

/-- Genuine logarithmic coordinate of a positive physical slot. -/
def slotLog {d : ℕ} (U n : Fin d → ℝ) : Point d :=
  fun i => Real.log (n i / U i)

theorem slotValue_slotLog {d : ℕ} (U n : Fin d → ℝ)
    (hU : ∀ i, 0 < U i) (hn : ∀ i, 0 < n i) :
    slotValue U (slotLog U n) = n := by
  funext i
  simp only [slotValue, slotLog]
  rw [Real.exp_log (div_pos (hn i) (hU i))]
  field_simp [(hU i).ne']
  ring

theorem slotLog_slotValue {d : ℕ} (U : Fin d → ℝ)
    (hU : ∀ i, 0 < U i) (z : Point d) :
    slotLog U (slotValue U z) = z := by
  funext i
  have heq : U i * Real.exp (z i) / U i = Real.exp (z i) := by
    field_simp [(hU i).ne']
  simp only [slotLog, slotValue, heq, Real.log_exp]

/-- The dyadic HB rectangle really lies in the old fixed chart, including
both closed endpoints. The window is not assumed one outside this rectangle. -/
theorem slotLog_mem_chart {d : ℕ} (U n : Fin d → ℝ)
    (hU : ∀ i, 0 < U i)
    (hn : ∀ i, U i ≤ n i ∧ n i ≤ 2 * U i) :
    ∀ i, 0 ≤ slotLog U n i ∧ slotLog U n i ≤ Real.log 2 := by
  intro i
  have hlo : 1 ≤ n i / U i := (le_div_iff₀ (hU i)).2 (hn i).1
  have hhi : n i / U i ≤ 2 := (div_le_iff₀ (hU i)).2 (by nlinarith [(hn i).2])
  exact ⟨Real.log_nonneg hlo,
    Real.log_le_log (lt_of_lt_of_le zero_lt_one hlo) hhi⟩

/-- The original W_T is a function of original labelled primes; each
label is a product of all HB variables in that label's group. -/
def originalPrimeWeight {d g : ℕ}
    (W : (Fin g → ℝ) → ℝ) (group : Fin d → Fin g)
    (n : Fin d → ℝ) : ℝ :=
  W (fun j => groupProduct group n j)

/-- Pull back W_T to the logarithmic HB rectangle without changing W_T.
The group bases are the products of the individual slot scales. -/
def pulledOriginalW {d g : ℕ}
    (W : (Fin g → ℝ) → ℝ) (U : Fin d → ℝ)
    (group : Fin d → Fin g) (z : Point d) : ℝ :=
  W (fun j => groupValue (groupBase U group) group z j)

/-- The log-chart pullback evaluates W_T on the exact physical original
groups, including unit and empty HB groups. -/
theorem pulledOriginalW_eq_original {d g : ℕ}
    (W : (Fin g → ℝ) → ℝ) (U : Fin d → ℝ)
    (group : Fin d → Fin g) (z : Point d) :
    pulledOriginalW W U group z =
      originalPrimeWeight W group (slotValue U z) := by
  apply congrArg W
  funext j
  exact groupValue_eq_slotProduct U group z j

/-- No special W formula is used: the inverse chart recovers the original
W_T on every positive physical HB tuple. -/
theorem pulledOriginalW_on_source {d g : ℕ}
    (W : (Fin g → ℝ) → ℝ) (U n : Fin d → ℝ)
    (hU : ∀ i, 0 < U i) (hn : ∀ i, 0 < n i)
    (group : Fin d → Fin g) :
    pulledOriginalW W U group (slotLog U n) =
      originalPrimeWeight W group n := by
  rw [pulledOriginalW_eq_original, slotValue_slotLog U n hU hn]

/-- Logarithms of the original groups are EXACT affine functions of the
logarithmic HB slot coordinates, not independently assigned offsets. -/
theorem originalGroup_log_affine {d g : ℕ}
    (U : Fin d → ℝ) (hU : ∀ i, 0 < U i)
    (group : Fin d → Fin g) (z : Point d) (j : Fin g) :
    Real.log (groupProduct group (slotValue U z) j) =
      Real.log (groupBase U group j) + groupSum group z j := by
  rw [← groupValue_eq_slotProduct U group z j]
  rw [groupValue,
    Real.log_mul (groupBase_pos U hU group j).ne' (Real.exp_pos _).ne',
    Real.log_exp]

/-- Every original-group product is preserved under the log inverse. -/
theorem originalGroup_on_source {d g : ℕ}
    (U n : Fin d → ℝ) (hU : ∀ i, 0 < U i)
    (hn : ∀ i, 0 < n i) (group : Fin d → Fin g) (j : Fin g) :
    groupValue (groupBase U group) group (slotLog U n) j =
      groupProduct group n j := by
  rw [groupValue_eq_slotProduct]
  change groupProduct group (slotValue U (slotLog U n)) j = _
  rw [slotValue_slotLog U n hU hn]

/-- The all-group complete product is the all-slot complete product:
there is no dropped factor, residual quotient, or double count. -/
theorem all_original_groups_product {d g : ℕ}
    (group : Fin d → Fin g) (n : Fin d → ℝ) :
    (∏ j, groupProduct group n j) = ∏ i, n i := by
  simp only [groupProduct]
  rw [Finset.prod_comm]
  apply Finset.prod_congr rfl
  intro i hi
  simp

end
end ImbalancedChen.P3PhysicalOriginalW
