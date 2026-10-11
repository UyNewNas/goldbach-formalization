import ImbalancedChen.PrimeOwnCubeAffineGates

/-!
# The six affine inequalities of an ordinary upper fifth candidate

Four rows impose strict decreasing order. The other two rows are the
inherited first and third cube tests. There is no fifth-cube row here;
that row must be attached separately at each old or new level.
-/

namespace ImbalancedChen

noncomputable section

open scoped Classical BigOperators
open Set

def ordinaryUpperFiveGateForms : Fin 6 → (Fin 5 → ℝ) →L[ℝ] ℝ :=
  let e (i : Fin 5) : (Fin 5 → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj i
  ![e 1 - e 0, e 2 - e 1, e 3 - e 2, e 4 - e 3,
    (3 : ℝ) • e 0, e 0 + e 1 + (3 : ℝ) • e 2]

def ordinaryUpperFiveGateBounds (old : ℝ) : Fin 6 → ℝ := ![0, 0, 0, 0, old, old]

theorem ordinaryUpperFiveGateForms_ne_zero : ∀ j, ordinaryUpperFiveGateForms j ≠ 0 := by
  intro j h
  have hh := congrArg (fun F : (Fin 5 → ℝ) →L[ℝ] ℝ => F (fun i => (i.val : ℝ) + 1)) h
  fin_cases j <;> norm_num [ordinaryUpperFiveGateForms] at hh

theorem mem_ordinaryUpperFiveGateRegion (old : ℝ) (t : Fin 5 → ℝ) :
    t ∈ primeAffineGateRegion ordinaryUpperFiveGateForms (ordinaryUpperFiveGateBounds old) ↔
      StrictAnti t ∧ 3 * t 0 < old ∧ t 0 + t 1 + 3 * t 2 < old := by
  have hanti : StrictAnti t ↔ t 1 < t 0 ∧ t 2 < t 1 ∧ t 3 < t 2 ∧ t 4 < t 3 := by
    constructor
    · intro h
      exact ⟨h (by decide), h (by decide), h (by decide), h (by decide)⟩
    · rintro ⟨h1, h2, h3, h4⟩
      apply Fin.strictAnti_iff_succ_lt.mpr
      intro i
      fin_cases i
      · exact h1
      · exact h2
      · exact h3
      · exact h4
  simp only [hanti]
  simp [primeAffineGateRegion, ordinaryUpperFiveGateForms, ordinaryUpperFiveGateBounds,
    Fin.forall_fin_succ, and_assoc]

/-- Strict ordering is preserved in both directions by the actual
target-dependent logarithmic coordinate dictionary. -/
theorem actualPrimeTupleLog_strictAnti_iff {d N : ℕ} (hN : 1 < N)
    (p : Fin d → ℕ) (hp : ∀ i, 0 < p i) :
    StrictAnti (actualPrimeTupleLog N p) ↔ StrictAnti p := by
  have hNr : (1 : ℝ) < N := by exact_mod_cast hN
  have hlt (i j : Fin d) : actualPrimeTupleLog N p i < actualPrimeTupleLog N p j ↔ p i < p j := by
    rw [← Real.rpow_lt_rpow_left_iff hNr,
      actualPrimeTupleLog_rpow hN p hp, actualPrimeTupleLog_rpow hN p hp]
    exact Nat.cast_lt
  exact ⟨fun h i j hij => (hlt j i).mp (h hij),
    fun h i j hij => (hlt j i).mpr (h hij)⟩

end

end ImbalancedChen
