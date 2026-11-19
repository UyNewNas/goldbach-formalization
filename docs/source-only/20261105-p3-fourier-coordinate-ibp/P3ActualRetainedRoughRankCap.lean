import ImbalancedChen.P3ActualRawActiveLevelTotientCap
import ImbalancedChen.FixedRoughCoefficients
import ImbalancedChen.RoughPrimeUniverse
import Mathlib.Tactic

/-!
P3.6, frozen manuscript
UyNewNas/chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b,
prime-product completion §3(T), §4(F).

The preceding raw physical reciprocal-totient bound still required
  ∀ b ∈ fixedRoughSupport, b ≤ B.
Here B comes from the ACTUAL retained first-exit leaf representation, not
from a newly invented rough modulus or from the full small presieve product.

Every chosen rough prime belongs to the original ordered roughPrimeUniverse
and is STRICTLY below its integer enumeration cap. If the retained leaves
are admitted with selected length ≤ K, the exact retained product b obeys
b ≤ cap^K. The producer's bound on K is still an INTERNAL obligation.

Without any rank admission, K may be taken as the full actual universe
length, giving an unconditional finite (but potentially enormous) cap.
That fallback is NOT a uniform polynomial-in-N or logarithmic PP budget.

The exact real raw rho and its original physical integer modulus/phi stay
unchanged. This file does not identify the full compiled integer rho_N,
pay the shifted divisor discrepancy, or assume an analytic PP estimate.
SOURCE_ONLY / UNCOMPILED / KERNEL_UNVERIFIED.
-/

namespace ImbalancedChen.P3ActualRetainedRoughRankCap

noncomputable section
open scoped Classical BigOperators
open ImbalancedChen
open ImbalancedChen.P3ActualRawPhysicalRhoTotientCap
open ImbalancedChen.P3ActualRawActiveLevelTotientCap
open ImbalancedChen.P3ActualSignedPairTotientCap

/-- Elementary finite list-product bound, with no primality requirement. -/
private theorem list_prod_le_cap_pow (cap : ℕ) :
    ∀ xs : List ℕ, (∀ p ∈ xs, p ≤ cap) →
      xs.prod ≤ cap ^ xs.length := by
  intro xs
  induction xs with
  | nil =>
      intro _
      simp
  | cons p ps ih =>
      intro h
      have hp : p ≤ cap := h p (by simp)
      have hps : ∀ q ∈ ps, q ≤ cap := by
        intro q hq
        exact h q (by simp [hq])
      calc
        (p :: ps).prod = p * ps.prod := by simp
        _ ≤ cap * cap ^ ps.length := Nat.mul_le_mul hp (ih hps)
        _ = cap ^ (p :: ps).length := by
          simp [pow_succ, mul_comm]

/-- An elementary power-monotonicity proof at a positive integer base.
It records why the condition 1 ≤ cap is necessary. -/
private theorem cap_pow_mono (cap n k : ℕ)
    (hcap : 1 ≤ cap) (hnk : n ≤ k) : cap ^ n ≤ cap ^ k := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hnk
  rw [pow_add]
  have ht : 1 ≤ cap ^ t := by
    have hp : 0 < cap := by omega
    have htpos : 0 < cap ^ t := pow_pos hp t
    omega
  simpa only [mul_one] using (Nat.mul_le_mul_left (cap ^ n) ht)

/-- A REAL retained leaf of the production rough tree has exact modulus
bounded by cap^K whenever its actual selected word has length ≤ K.
No assumption is made about the values or signs of its coefficients. -/
theorem retained_leaf_prod_le_rank_cap
    (retainOdd : List ℕ → Bool) (N cap : ℕ) (w z : ℝ)
    (leaf : FirstExitLeaf ℕ)
    (hleaf : leaf ∈ oddFirstExitRetainedLeaves retainOdd (fun _ => (1 : ℝ))
      (roughPrimeUniverse N cap w z))
    (K : ℕ) (hcap : 1 ≤ cap) (hlen : leaf.selected.length ≤ K) :
    leaf.selected.prod ≤ cap ^ K := by
  have hsub : leaf.selected.reverse <+ roughPrimeUniverse N cap w z :=
    mem_oddFirstExitRetainedLeaves_selected_reverse_sublist
      retainOdd (fun _ => (1 : ℝ)) (roughPrimeUniverse N cap w z) leaf hleaf
  have hbound : ∀ p ∈ leaf.selected, p ≤ cap := by
    intro p hp
    have hrev : p ∈ leaf.selected.reverse := by simpa using hp
    have hcarrier : p ∈ roughPrimeUniverse N cap w z := hsub.subset hrev
    exact (mem_roughPrimeUniverse.mp hcarrier).1.le
  exact (list_prod_le_cap_pow cap leaf.selected hbound).trans
    (cap_pow_mono cap leaf.selected.length K hcap hlen)

/-- Actual fixed first-exit ROUGH support cap, derived from a rank
admission on actual retained leaves rather than an abstract bound on b.
This is the precise internal interface needed from the causal producer. -/
theorem fixed_rough_support_le_rank_cap
    (retainOdd : List ℕ → Bool) (N cap : ℕ) (w z : ℝ) (K : ℕ)
    (hcap : 1 ≤ cap)
    (hrank : ∀ leaf ∈
      oddFirstExitRetainedLeaves retainOdd (fun _ => (1 : ℝ))
        (roughPrimeUniverse N cap w z), leaf.selected.length ≤ K)
    {b : ℕ} (hb : b ∈ fixedRoughSupport retainOdd N cap w z) :
    b ≤ cap ^ K := by
  change b ∈ oddFirstExitRetainedModuli retainOdd (fun _ => (1 : ℝ))
    (roughPrimeUniverse N cap w z) at hb
  obtain ⟨leaf, hleaf, hprod⟩ :=
    (mem_oddFirstExitRetainedModuli retainOdd (fun _ => (1 : ℝ))
      (roughPrimeUniverse N cap w z) b).mp hb
  calc
    b = leaf.selected.prod := hprod.symm
    _ ≤ cap ^ K :=
      retained_leaf_prod_le_rank_cap retainOdd N cap w z leaf hleaf
        K hcap (hrank leaf hleaf)

/-- Every actual retained leaf is a subword of the ordered rough universe.
Thus the producer always has K = universe.length, although this K is not
necessarily fixed or O(1) in N. -/
theorem fixed_rough_support_le_universe_power
    (retainOdd : List ℕ → Bool) (N cap : ℕ) (w z : ℝ)
    (hcap : 1 ≤ cap) {b : ℕ}
    (hb : b ∈ fixedRoughSupport retainOdd N cap w z) :
    b ≤ cap ^ (roughPrimeUniverse N cap w z).length := by
  apply fixed_rough_support_le_rank_cap retainOdd N cap w z
    (roughPrimeUniverse N cap w z).length hcap _ hb
  intro leaf hleaf
  have hsub := mem_oddFirstExitRetainedLeaves_selected_reverse_sublist
    retainOdd (fun _ => (1 : ℝ)) (roughPrimeUniverse N cap w z) leaf hleaf
  simpa using hsub.length_le

/-- The exact RAW physical rho mass is now controlled by the TRUE rough
producer's selected-rank K, not an arbitrary pointwise rough support cap.
The Rosser factor is controlled by the actual strict level L ≤ A. -/
theorem actual_raw_physical_mass_le_retained_rank_caps
    (retainOdd : List ℕ → Bool) (N cap A K : ℕ) (w z L : ℝ)
    (hLA : L ≤ (A : ℝ)) (hcap : 1 ≤ cap)
    (hrank : ∀ leaf ∈
      oddFirstExitRetainedLeaves retainOdd (fun _ => (1 : ℝ))
        (roughPrimeUniverse N cap w z), leaf.selected.length ≤ K) :
    actualRawPhysicalTotientMass retainOdd N cap w z L ≤
      logTotientCap A * logTotientCap (cap ^ K) := by
  exact actual_raw_physical_mass_le_active_level_caps
    retainOdd N cap A (cap ^ K) w z L hLA
    (fun b hb => fixed_rough_support_le_rank_cap
      retainOdd N cap w z K hcap hrank hb)

/-- Fully finite fallback without a rank premise. It is intentionally NOT
called a uniform log(N) estimate; the universe length can grow with N. -/
theorem actual_raw_physical_mass_le_universe_length_caps
    (retainOdd : List ℕ → Bool) (N cap A : ℕ) (w z L : ℝ)
    (hLA : L ≤ (A : ℝ)) (hcap : 1 ≤ cap) :
    actualRawPhysicalTotientMass retainOdd N cap w z L ≤
      logTotientCap A *
        logTotientCap (cap ^ (roughPrimeUniverse N cap w z).length) := by
  exact actual_raw_physical_mass_le_active_level_caps
    retainOdd N cap A (cap ^ (roughPrimeUniverse N cap w z).length)
    w z L hLA
    (fun b hb => fixed_rough_support_le_universe_power
      retainOdd N cap w z hcap hb)

end
end ImbalancedChen.P3ActualRetainedRoughRankCap
