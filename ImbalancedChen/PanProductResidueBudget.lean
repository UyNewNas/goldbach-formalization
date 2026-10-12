import ImbalancedChen.PanProductStrips
import ImbalancedChen.ResidueSelectorBudget

/-!
# Primitive-residue budgets for product-strip Pan prefixes

The bounded Pan supplier is uniform over a canonical primitive residue at
each modulus.  The manuscript target is the fixed integer `N`, which need not
itself lie below the modulus.  This file proves that the selector
`d ↦ N % d` is canonical whenever `N` is coprime to every positive modulus in
the sum, and transports prefix and strip errors back to the literal target
residue `N`.

For a product strip, separate uniform budgets at the upper and lower closed
prefixes give the sum of those two budgets.  There is no factor counting
moduli or residue classes, and no use of coprimality with either product
scale.  These are finite selection and triangle identities; no distribution
estimate is asserted here.
-/

namespace ImbalancedChen

noncomputable section

open scoped BigOperators

/-- Replacing the target by its canonical representative preserves the
right-hand side of every natural-number congruence, including at modulus
zero.  Positivity is needed only later for primitive-residue membership. -/
@[simp] theorem modEq_target_mod_right (m N d : ℕ) :
    Nat.ModEq d m (N % d) ↔ Nat.ModEq d m N := by
  simp only [Nat.ModEq, Nat.mod_mod]

/-- Reduction of the target residue does not change a product-prefix AP
count. -/
@[simp] theorem panProductPrefixAPCount_residue_mod
    (A₁ A₂ Y a d : ℕ) :
    panProductPrefixAPCount A₁ A₂ Y (a % d) d =
      panProductPrefixAPCount A₁ A₂ Y a d := by
  classical
  unfold panProductPrefixAPCount
  have hset :
      (panProductPrefixPairs A₁ A₂ Y).filter
          (fun p => Nat.ModEq d (p.1 * p.2) (a % d)) =
        (panProductPrefixPairs A₁ A₂ Y).filter
          (fun p => Nat.ModEq d (p.1 * p.2) a) := by
    ext p
    rw [Finset.mem_filter, Finset.mem_filter]
    simp only [Nat.ModEq, Nat.mod_mod]
  rw [hset]

/-- The same reduction is harmless for a product-strip AP count. -/
@[simp] theorem panProductStripAPCount_residue_mod
    (A₁ A₂ Y₀ Y₁ a d : ℕ) :
    panProductStripAPCount A₁ A₂ Y₀ Y₁ (a % d) d =
      panProductStripAPCount A₁ A₂ Y₀ Y₁ a d := by
  classical
  unfold panProductStripAPCount
  have hset :
      (panProductStripPairs A₁ A₂ Y₀ Y₁).filter
          (fun p => Nat.ModEq d (p.1 * p.2) (a % d)) =
        (panProductStripPairs A₁ A₂ Y₀ Y₁).filter
          (fun p => Nat.ModEq d (p.1 * p.2) a) := by
    ext p
    rw [Finset.mem_filter, Finset.mem_filter]
    simp only [Nat.ModEq, Nat.mod_mod]
  rw [hset]

/-- A residue-independent prefix main term makes the corresponding analytic
error invariant under reducing the target residue. -/
@[simp] theorem panProductPrefixAnalyticError_residue_mod
    (mainTerm : ℝ → ℝ) (A₁ A₂ Y a d : ℕ) :
    panProductPrefixAnalyticError mainTerm A₁ A₂ Y (a % d) d =
      panProductPrefixAnalyticError mainTerm A₁ A₂ Y a d := by
  unfold panProductPrefixAnalyticError
  rw [panProductPrefixAPCount_residue_mod]

/-- The corresponding strip error is likewise invariant under reduction of
the target residue. -/
@[simp] theorem panProductStripAnalyticError_residue_mod
    (mainTerm : ℝ → ℝ) (A₁ A₂ Y₀ Y₁ a d : ℕ) :
    panProductStripAnalyticError mainTerm A₁ A₂ Y₀ Y₁ (a % d) d =
      panProductStripAnalyticError mainTerm A₁ A₂ Y₀ Y₁ a d := by
  unfold panProductStripAnalyticError
  rw [panProductStripAPCount_residue_mod]

/-- The fixed target `N` supplies a canonical primitive residue selector at
every positive modulus coprime to `N`.  The scale `Y` is deliberately absent
from the statement. -/
theorem target_mod_mem_finiteReducedResidues
    (N d : ℕ) (hd : 0 < d) (hNd : Nat.Coprime N d) :
    N % d ∈ finiteReducedResidues d :=
  (mod_mem_finiteReducedResidues_iff N d hd).mpr hNd

/-- A uniform selector estimate for one closed prefix controls the literal
target residue.  No recentering is used and therefore no factor two occurs. -/
theorem sum_abs_panProductPrefixAnalyticError_target_le
    (S : Finset ℕ) (mainTerm : ℝ → ℝ)
    (A₁ A₂ Y N : ℕ) (B : ℝ)
    (hS : ∀ d ∈ S, 0 < d)
    (hN : ∀ d ∈ S, Nat.Coprime N d)
    (hUniform : ∀ a : ℕ → ℕ,
      (∀ d ∈ S, a d ∈ finiteReducedResidues d) →
      (∑ d ∈ S,
        |panProductPrefixAnalyticError mainTerm A₁ A₂ Y (a d) d|) ≤ B) :
    (∑ d ∈ S,
      |panProductPrefixAnalyticError mainTerm A₁ A₂ Y N d|) ≤ B := by
  let a : ℕ → ℕ := fun d => N % d
  have ha : ∀ d ∈ S, a d ∈ finiteReducedResidues d := by
    intro d hd
    exact target_mod_mem_finiteReducedResidues N d (hS d hd) (hN d hd)
  have h := hUniform a ha
  simpa only [a, panProductPrefixAnalyticError_residue_mod] using h

/-- Two independent primitive-selector Pan budgets, one at each closed
product scale, control the literal strict-lower/closed-upper strip. -/
theorem sum_abs_panProductStripAnalyticError_target_le
    (S : Finset ℕ) (mainTerm : ℝ → ℝ)
    (A₁ A₂ Y₀ Y₁ N : ℕ) (B₀ B₁ : ℝ)
    (hY : Y₀ ≤ Y₁)
    (hS : ∀ d ∈ S, 0 < d)
    (hN : ∀ d ∈ S, Nat.Coprime N d)
    (hLower : ∀ a : ℕ → ℕ,
      (∀ d ∈ S, a d ∈ finiteReducedResidues d) →
      (∑ d ∈ S,
        |panProductPrefixAnalyticError mainTerm A₁ A₂ Y₀ (a d) d|) ≤ B₀)
    (hUpper : ∀ a : ℕ → ℕ,
      (∀ d ∈ S, a d ∈ finiteReducedResidues d) →
      (∑ d ∈ S,
        |panProductPrefixAnalyticError mainTerm A₁ A₂ Y₁ (a d) d|) ≤ B₁) :
    (∑ d ∈ S,
      |panProductStripAnalyticError mainTerm A₁ A₂ Y₀ Y₁ N d|) ≤
        B₁ + B₀ := by
  calc
    (∑ d ∈ S,
        |panProductStripAnalyticError mainTerm A₁ A₂ Y₀ Y₁ N d|) ≤
        ∑ d ∈ S,
          (|panProductPrefixAnalyticError mainTerm A₁ A₂ Y₁ N d| +
            |panProductPrefixAnalyticError mainTerm A₁ A₂ Y₀ N d|) := by
      apply Finset.sum_le_sum
      intro d _
      exact abs_panProductStripAnalyticError_le
        mainTerm A₁ A₂ Y₀ Y₁ N d hY
    _ = (∑ d ∈ S,
          |panProductPrefixAnalyticError mainTerm A₁ A₂ Y₁ N d|) +
        ∑ d ∈ S,
          |panProductPrefixAnalyticError mainTerm A₁ A₂ Y₀ N d| := by
      rw [Finset.sum_add_distrib]
    _ ≤ B₁ + B₀ := add_le_add
      (sum_abs_panProductPrefixAnalyticError_target_le
        S mainTerm A₁ A₂ Y₁ N B₁ hS hN hUpper)
      (sum_abs_panProductPrefixAnalyticError_target_le
        S mainTerm A₁ A₂ Y₀ N B₀ hS hN hLower)

end

end ImbalancedChen
