import ImbalancedChen.P4AOriginalFull87TerminalDepthBudget

/-!
SOURCE ONLY / UNCOMPILED / UNEVALUATED / ZERO KERNEL CREDIT.

At EVERY real ordinary terminal leaf below a changed original87 occurrence,
the original small Rosser factor a and the ENTIRE rough selected product r
are both target-coprime and coprime to each other. The physical modulus is
the same a*r used by the signed beta attachment. Its exact reciprocal
totient therefore splits into small and rough factors; there is no new
policy, changed owner, separate mean assumption, or analytic reserve claim.
-/

namespace ImbalancedChen.P4AOriginalFull87TerminalDensitySplit
noncomputable section
open scoped Classical BigOperators
open P1Pair12RetainedSignedSource
open P4AOriginalFull87SourceDictionary (Cell)
open P4AOriginalFull87ChangedFrontierBudget (changedStates)
open P4AOriginalFull87PopulationVariation (absoluteAttached)
open P4AOriginalFull87EighthPrimeMeanLedger (densityTest)
open P4AOriginalFull87ActualTerminalFactors

/-- All selected primes, including post-eighth descendants, avoid N. -/
theorem terminal_rough_coprime_target
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z : ℝ) (c : Cell) (s : FirstExitDepthState ℕ)
    (hs : s ∈ changedStates delta n e q om N cap w z c)
    (R : Bool → List ℕ → Bool) (leaf : FirstExitLeaf ℕ)
    (hl : leaf ∈ firstExitRetainedLeaves R (fun _ => 1)
      s.selectedPrefix s.positive s.mass s.remaining) :
    leaf.selected.prod.Coprime N := by
  obtain ⟨hnodup, hdata⟩ :=
    actual_terminal_metadata delta n e q om N cap w z c s hs R leaf hl
  have hprod : (∏ p ∈ leaf.selected.toFinset, p) = leaf.selected.prod := by
    simpa using List.prod_toFinset (fun p : ℕ => p) hnodup
  rw [← hprod, Nat.coprime_prod_left_iff]
  intro p hp
  have h := hdata p (List.mem_toFinset.mp hp)
  exact h.1.coprime_iff_not_dvd.mpr h.2.1

/-- The true small divisor and actual terminal rough product are coprime. -/
theorem terminal_small_rough_coprime
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z : ℝ) (c : Cell) (s : FirstExitDepthState ℕ)
    (hs : s ∈ changedStates delta n e q om N cap w z c)
    (R : Bool → List ℕ → Bool) (leaf : FirstExitLeaf ℕ)
    (hl : leaf ∈ firstExitRetainedLeaves R (fun _ => 1)
      s.selectedPrefix s.positive s.mass s.remaining)
    (a : ℕ) (ha : a ∈ actualSmallRosserSupport N cap w) :
    a.Coprime leaf.selected.prod := by
  obtain ⟨hnodup, hdata⟩ :=
    actual_terminal_metadata delta n e q om N cap w z c s hs R leaf hl
  have hprod : leaf.selected.prod ≠ 0 := by
    apply List.prod_ne_zero
    intro hzero
    exact (hdata 0 hzero).1.ne_zero rfl
  have hset : leaf.selected.prod.primeFactors = leaf.selected.toFinset :=
    terminal_selected_factor_set leaf.selected hnodup (fun p hp => (hdata p hp).1)
  have hrough : RoughPrimeSupportedAt w leaf.selected.prod := by
    refine ⟨hprod, ?_⟩
    intro p hp
    rw [hset] at hp
    exact (hdata p (List.mem_toFinset.mp hp)).2.2.1
  exact smallPrimeSupportedAt_coprime_roughPrimeSupportedAt
    (actualSmallRosserSupport_smallPrimeSupportedAt N cap w ha) hrough

/-- This is the original FULL physical modulus, not just the rough part. -/
theorem terminal_full_coprime_target
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z : ℝ) (c : Cell) (s : FirstExitDepthState ℕ)
    (hs : s ∈ changedStates delta n e q om N cap w z c)
    (R : Bool → List ℕ → Bool) (leaf : FirstExitLeaf ℕ)
    (hl : leaf ∈ firstExitRetainedLeaves R (fun _ => 1)
      s.selectedPrefix s.positive s.mass s.remaining)
    (a : ℕ) (ha : a ∈ actualSmallRosserSupport N cap w) :
    (a * leaf.selected.prod).Coprime N := by
  exact (actualSmallRosserSupport_coprime_target N cap w ha).mul
    (terminal_rough_coprime_target delta n e q om N cap w z c s hs R leaf hl)

/-- Exact totient multiplicativity at the genuine terminal full modulus. -/
theorem terminal_full_totient_mul
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z : ℝ) (c : Cell) (s : FirstExitDepthState ℕ)
    (hs : s ∈ changedStates delta n e q om N cap w z c)
    (R : Bool → List ℕ → Bool) (leaf : FirstExitLeaf ℕ)
    (hl : leaf ∈ firstExitRetainedLeaves R (fun _ => 1)
      s.selectedPrefix s.positive s.mass s.remaining)
    (a : ℕ) (ha : a ∈ actualSmallRosserSupport N cap w) :
    Nat.totient (a * leaf.selected.prod) =
      Nat.totient a * Nat.totient leaf.selected.prod := by
  exact Nat.totient_mul
    (terminal_small_rough_coprime delta n e q om N cap w z c s hs R leaf hl a ha)

/-- No approximation: 1/φ(a*r)=(1/φ(a))*(1/φ(r)) on the same leaf. -/
theorem terminal_full_density_mul
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z : ℝ) (c : Cell) (s : FirstExitDepthState ℕ)
    (hs : s ∈ changedStates delta n e q om N cap w z c)
    (R : Bool → List ℕ → Bool) (leaf : FirstExitLeaf ℕ)
    (hl : leaf ∈ firstExitRetainedLeaves R (fun _ => 1)
      s.selectedPrefix s.positive s.mass s.remaining)
    (a : ℕ) (ha : a ∈ actualSmallRosserSupport N cap w) :
    densityTest (a * leaf.selected.prod) =
      densityTest a * densityTest leaf.selected.prod := by
  unfold densityTest
  rw [terminal_full_totient_mul delta n e q om N cap w z c s hs R leaf hl a ha]
  push_cast
  simp only [one_div, mul_inv_rev]

/-- Keep the SAME sign's original small Rosser beta, pull out the rough
factor only after the actual entire terminal history is selected. -/
theorem terminal_absolute_beta_density_split
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (c : Cell) (s : FirstExitDepthState ℕ)
    (hs : s ∈ changedStates delta n e q om N cap w z c)
    (R : Bool → List ℕ → Bool) (leaf : FirstExitLeaf ℕ)
    (hl : leaf ∈ firstExitRetainedLeaves R (fun _ => 1)
      s.selectedPrefix s.positive s.mass s.remaining) :
    absoluteAttached N cap w L densityTest leaf.positive leaf.selected =
      (∑ a ∈ actualSmallRosserSupport N cap w,
        |if leaf.positive then actualSmallRosserPlus N cap w L a
         else actualSmallRosserMinus N cap w L a| * densityTest a) *
        densityTest leaf.selected.prod := by
  unfold absoluteAttached
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a ha
  rw [terminal_full_density_mul delta n e q om N cap w z c s hs R leaf hl a ha]
  ring

/-- Pinned Mathlib's Euler product is RATIONAL here, not silently cast
to Real; the full true terminal selected prime set has no duplicate. -/
theorem terminal_rough_euler_product_Q
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z : ℝ) (c : Cell) (s : FirstExitDepthState ℕ)
    (hs : s ∈ changedStates delta n e q om N cap w z c)
    (R : Bool → List ℕ → Bool) (leaf : FirstExitLeaf ℕ)
    (hl : leaf ∈ firstExitRetainedLeaves R (fun _ => 1)
      s.selectedPrefix s.positive s.mass s.remaining) :
    (Nat.totient leaf.selected.prod : ℚ) =
      (leaf.selected.prod : ℚ) *
        ∏ p ∈ leaf.selected.toFinset, (1 - (p : ℚ)⁻¹) := by
  obtain ⟨hnodup, hdata⟩ :=
    actual_terminal_metadata delta n e q om N cap w z c s hs R leaf hl
  simpa only [terminal_selected_factor_set leaf.selected hnodup
    (fun p hp => (hdata p hp).1)] using
    Nat.totient_eq_mul_prod_factors leaf.selected.prod

/-- The TRUE terminal-depth plus small-factor population envelope also
separates; nothing truncates the continuation at the eighth frontier. -/
theorem terminal_depth_beta_density_split
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (c : Cell) (s : FirstExitDepthState ℕ)
    (hs : s ∈ changedStates delta n e q om N cap w z c)
    (R : Bool → List ℕ → Bool) (leaf : FirstExitLeaf ℕ)
    (hl : leaf ∈ firstExitRetainedLeaves R (fun _ => 1)
      s.selectedPrefix s.positive s.mass s.remaining) :
    P4AOriginalFull87TerminalDepthBudget.depthAttached
        N cap w L leaf.positive leaf.selected =
      (∑ a ∈ actualSmallRosserSupport N cap w,
        |if leaf.positive then actualSmallRosserPlus N cap w L a
         else actualSmallRosserMinus N cap w L a| *
        (((a.primeFactors.card + leaf.selected.length : ℕ) : ℝ) * densityTest a)) *
      densityTest leaf.selected.prod := by
  unfold P4AOriginalFull87TerminalDepthBudget.depthAttached
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a ha
  rw [terminal_full_density_mul delta n e q om N cap w z c s hs R leaf hl a ha]
  ring

end
end ImbalancedChen.P4AOriginalFull87TerminalDensitySplit
