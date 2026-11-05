import ImbalancedChen.P4AOriginalFull87FactorPopulation
import ImbalancedChen.FirstExitFrontierInvariants
import ImbalancedChen.ActualSmallRosser

/-!
SOURCE ONLY / UNCOMPILED / UNEVALUATED / NO KERNEL CREDIT.

A genuine eighth changed occurrence is followed through either ACTUAL ordinary
continuation, including all subsequent rough-prime selections. The resulting
terminal full modulus is a *small Rosser divisor* times the entire terminal
selected-prime product, not merely the eight-prime frontier product.

At every such terminal leaf, the strict (< w) small support and inclusive
(>= w) rough support are coprime, so its distinct-prime population is EXACTLY
omega(small) + terminal selected length. This remains true for a full modulus
larger than N. If the enumeration cap is at most N, ALL its prime factors
are in the inclusive prime prefix, without an invalid assumption d <= N.

This finite original-source lemma is not a uniform o(1) payment. Ordinary
continuations may select MORE THAN eight primes: the terminal depth must
not be replaced by 8 in the full-q arithmetic variation budget.
-/

namespace ImbalancedChen.P4AOriginalFull87ActualTerminalFactors
noncomputable section
open scoped Classical BigOperators
open P4AOriginalFull87SourceDictionary (Cell)
open P4AOriginalFull87SourceDispatch (point8)
open P4AOriginalFull87FiniteEighthCap (finiteCap)
open P4AOriginalFull87EighthKernelIntegration (actualParent)
open P4AOriginalFull87OwnedEighthSource (frontier)
open P4AOriginalFull87ChangedFrontierBudget (changedStates)
open P4AOriginalFull87FactorPopulation
open P4AOriginalFull87EighthPrimeMeanLedger (densityTest)

/-- A genuinely changed occurrence is in the original filtered sixth
frontier. This does not replace ownerAtPrefix, trim or the admission tree. -/
theorem changed_mem_real_frontier
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z : ℝ) (c : Cell) (s : FirstExitDepthState ℕ)
    (hs : s ∈ changedStates delta n e q om N cap w z c) :
    s ∈ frontier n e q om N cap w z := by
  unfold changedStates at hs
  have howner := (List.mem_filter.mp hs).1
  rw [P4AOriginalFull87OwnedEighthSource.states_eq_owner_filter] at howner
  exact (List.mem_filter.mp howner).1

/-- EVERY terminal leaf of ANY genuine ordinary continuation from a changed
state still consists exclusively of the original decreasing rough-prime
carrier. The existing recursion, not a new abstract selector, proves this. -/
theorem actual_terminal_selected_sublist
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z : ℝ) (c : Cell) (s : FirstExitDepthState ℕ)
    (hs : s ∈ changedStates delta n e q om N cap w z c)
    (R : Bool → List ℕ → Bool) (leaf : FirstExitLeaf ℕ)
    (hl : leaf ∈ firstExitRetainedLeaves R (fun _ => 1)
      s.selectedPrefix s.positive s.mass s.remaining) :
    leaf.selected.reverse <+ roughPrimeUniverse N cap w z := by
  have hfr : s ∈ frontier n e q om N cap w z :=
    changed_mem_real_frontier delta n e q om N cap w z c s hs
  have hprefix : s.selectedPrefix.reverse ++ s.remaining <+
      roughPrimeUniverse N cap w z := by
    have h := firstExitDepthFrontier_selected_remaining_sublist
      8 (P4AOriginalFull87LicensedSixthPolicy.sixthPolicy
        n e q om (N : ℝ)) (fun _ : ℕ => 1)
      [] (roughPrimeUniverse N cap w z) true 1 s
      (by simpa only [frontier] using hfr)
    simpa using h
  exact (firstExitRetainedLeaves_selected_reverse_sublist R
    (fun _ : ℕ => 1) s.selectedPrefix s.remaining
    s.positive s.mass leaf hl).trans hprefix

/-- The terminal prefix has no duplicated prime, excludes target primes,
and each selected prime lies in [w,cap). These are inherited from the
REAL rough-prime carrier, even if the continuation selects beyond rank 8. -/
theorem actual_terminal_metadata
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z : ℝ) (c : Cell) (s : FirstExitDepthState ℕ)
    (hs : s ∈ changedStates delta n e q om N cap w z c)
    (R : Bool → List ℕ → Bool) (leaf : FirstExitLeaf ℕ)
    (hl : leaf ∈ firstExitRetainedLeaves R (fun _ => 1)
      s.selectedPrefix s.positive s.mass s.remaining) :
    leaf.selected.Nodup ∧
      (∀ p ∈ leaf.selected,
        p.Prime ∧ ¬p ∣ N ∧ w ≤ (p : ℝ) ∧ p < cap) := by
  have hsub := actual_terminal_selected_sublist
    delta n e q om N cap w z c s hs R leaf hl
  have hnodup : leaf.selected.Nodup := by
    have hrev := (roughPrimeUniverse_nodup N cap w z).sublist hsub
    simpa using hrev
  refine ⟨hnodup, ?_⟩
  intro p hp
  have hpCarrier : p ∈ roughPrimeUniverse N cap w z :=
    hsub.subset (by simpa using hp)
  exact ⟨mem_roughPrimeUniverse_prime hpCarrier,
    mem_roughPrimeUniverse_not_dvd hpCarrier,
    mem_roughPrimeUniverse_lower hpCarrier,
    (mem_roughPrimeUniverse.mp hpCarrier).1⟩

/-- Prime factors of a product of two nonzero natural numbers form the
SET union of their factors, independently of squarefreeness. -/
theorem factors_mul_union (a b : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) :
    (a * b).primeFactors = a.primeFactors ∪ b.primeFactors := by
  ext p
  simp only [Nat.mem_primeFactors, Finset.mem_union]
  constructor
  · rintro ⟨hp, hpd, _⟩
    rcases hp.dvd_mul.mp hpd with hpa | hpb
    · exact Or.inl ⟨hp, hpa, ha⟩
    · exact Or.inr ⟨hp, hpb, hb⟩
  · rintro (⟨hp, hpa, _⟩ | ⟨hp, hpb, _⟩)
    · exact ⟨hp, dvd_mul_of_dvd_left hpa b, mul_ne_zero ha hb⟩
    · exact ⟨hp, by simpa [mul_comm] using
        (dvd_mul_of_dvd_left hpb a), mul_ne_zero ha hb⟩

/-- A duplicate-free list of actual prime labels has exactly its list
labels as the distinct prime factors of its product. -/
theorem terminal_selected_factor_set
    (xs : List ℕ) (hnodup : xs.Nodup)
    (hprime : ∀ p ∈ xs, Nat.Prime p) :
    xs.prod.primeFactors = xs.toFinset := by
  have hprod : (∏ p ∈ xs.toFinset, p) = xs.prod := by
    simpa using List.prod_toFinset (fun p : ℕ => p) hnodup
  rw [← hprod]
  exact Nat.primeFactors_prod fun p hp =>
    hprime p (List.mem_toFinset.mp hp)

/-- The full physical modulus at EACH actual terminal leaf has exact
small/rough factor union. In particular it is nonzero. -/
theorem actual_terminal_full_factor_set
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z : ℝ) (c : Cell) (s : FirstExitDepthState ℕ)
    (hs : s ∈ changedStates delta n e q om N cap w z c)
    (R : Bool → List ℕ → Bool) (leaf : FirstExitLeaf ℕ)
    (hl : leaf ∈ firstExitRetainedLeaves R (fun _ => 1)
      s.selectedPrefix s.positive s.mass s.remaining)
    (a : ℕ) (ha : a ∈ actualSmallRosserSupport N cap w) :
    (a * leaf.selected.prod).primeFactors =
      a.primeFactors ∪ leaf.selected.toFinset := by
  obtain ⟨hnodup, hdata⟩ :=
    actual_terminal_metadata delta n e q om N cap w z c s hs R leaf hl
  have hb : leaf.selected.prod ≠ 0 := by
    apply List.prod_ne_zero
    intro hzero
    exact (hdata 0 hzero).1.ne_zero rfl
  have hsmall := actualSmallRosserSupport_smallPrimeSupportedAt N cap w ha
  rw [factors_mul_union a leaf.selected.prod hsmall.1 hb]
  exact congrArg (fun t : Finset ℕ => a.primeFactors ∪ t)
    (terminal_selected_factor_set leaf.selected hnodup (fun p hp => (hdata p hp).1))

/-- On the EXACT terminal full modulus, strict small and inclusive rough
cutoffs imply no factor overlap. Each later selected rough prime is counted
ONCE. The count is omega(a)+TERMINAL length, NOT omega(a)+8. -/
theorem actual_terminal_full_factor_card
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z : ℝ) (c : Cell) (s : FirstExitDepthState ℕ)
    (hs : s ∈ changedStates delta n e q om N cap w z c)
    (R : Bool → List ℕ → Bool) (leaf : FirstExitLeaf ℕ)
    (hl : leaf ∈ firstExitRetainedLeaves R (fun _ => 1)
      s.selectedPrefix s.positive s.mass s.remaining)
    (a : ℕ) (ha : a ∈ actualSmallRosserSupport N cap w) :
    (a * leaf.selected.prod).primeFactors.card =
      a.primeFactors.card + leaf.selected.length := by
  obtain ⟨hnodup, hdata⟩ :=
    actual_terminal_metadata delta n e q om N cap w z c s hs R leaf hl
  have hb : leaf.selected.prod ≠ 0 := by
    apply List.prod_ne_zero
    intro hzero
    exact (hdata 0 hzero).1.ne_zero rfl
  have hf : leaf.selected.prod.primeFactors = leaf.selected.toFinset :=
    terminal_selected_factor_set leaf.selected hnodup
      (fun p hp => (hdata p hp).1)
  have hr : RoughPrimeSupportedAt w leaf.selected.prod := by
    refine ⟨hb, ?_⟩
    intro p hp
    rw [hf] at hp
    exact (hdata p (List.mem_toFinset.mp hp)).2.2.1
  have hsmall := actualSmallRosserSupport_smallPrimeSupportedAt N cap w ha
  have hdis : Disjoint a.primeFactors leaf.selected.toFinset := by
    have hraw : Disjoint a.primeFactors leaf.selected.prod.primeFactors :=
      (Nat.disjoint_primeFactors hsmall.1 hr.1).mpr
        (smallPrimeSupportedAt_coprime_roughPrimeSupportedAt hsmall hr)
    simpa only [hf] using hraw
  rw [actual_terminal_full_factor_set delta n e q om N cap w z
    c s hs R leaf hl a ha, Finset.card_union_of_disjoint hdis]
  have hcard : leaf.selected.toFinset.card = leaf.selected.length := by
    simpa using List.toFinset_card_of_nodup hnodup
  rw [hcard]

/-- An effective support-specific bound for the PREVIOUS unchanged
factorModulusBudgetTest, evaluated at any true terminal full-q attachment.
No assertion about normalization, reserve payment or future branch depth. -/
theorem actual_terminal_factor_budget
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z : ℝ) (c : Cell) (s : FirstExitDepthState ℕ)
    (hs : s ∈ changedStates delta n e q om N cap w z c)
    (R : Bool → List ℕ → Bool) (leaf : FirstExitLeaf ℕ)
    (hl : leaf ∈ firstExitRetainedLeaves R (fun _ => 1)
      s.selectedPrefix s.positive s.mass s.remaining)
    (a : ℕ) (ha : a ∈ actualSmallRosserSupport N cap w) :
    factorModulusBudgetTest N (a * leaf.selected.prod) ≤
      ((a.primeFactors.card + leaf.selected.length : ℕ) : ℝ) *
        densityTest (a * leaf.selected.prod) := by
  have hsmall := actualSmallRosserSupport_smallPrimeSupportedAt N cap w ha
  have hdata := (actual_terminal_metadata delta n e q om N cap w z
    c s hs R leaf hl).2
  have hb : leaf.selected.prod ≠ 0 := by
    apply List.prod_ne_zero
    intro hzero
    exact (hdata 0 hzero).1.ne_zero rfl
  have hcap : primeCountCap N (a * leaf.selected.prod) ≤
      a.primeFactors.card + leaf.selected.length := by
    calc
      primeCountCap N (a * leaf.selected.prod) ≤
          (a * leaf.selected.prod).primeFactors.card :=
        primeCountCap_le_factor_card N _ (mul_ne_zero hsmall.1 hb)
      _ = _ :=
        actual_terminal_full_factor_card delta n e q om N cap w z
          c s hs R leaf hl a ha
  have hreal : (primeCountCap N (a * leaf.selected.prod) : ℝ) ≤
      ((a.primeFactors.card + leaf.selected.length : ℕ) : ℝ) := by
    exact_mod_cast hcap
  unfold factorModulusBudgetTest
  exact mul_le_mul_of_nonneg_right hreal (by unfold densityTest; positivity)

/-- An IMPORTANT refinement of the earlier conditional d<=N lemma:
even when the complete modulus is LARGER than N, if the original finite
enumeration cap is <=N, every one of its prime factors is <=N and the
actual inclusive-prefix modulus-prime defect has EXACT terminal population.
The cap<=N condition is explicit; it is NOT silently assumed. -/
theorem actual_terminal_prime_population_of_cap_le_N
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z : ℝ) (hcapN : cap ≤ N)
    (c : Cell) (s : FirstExitDepthState ℕ)
    (hs : s ∈ changedStates delta n e q om N cap w z c)
    (R : Bool → List ℕ → Bool) (leaf : FirstExitLeaf ℕ)
    (hl : leaf ∈ firstExitRetainedLeaves R (fun _ => 1)
      s.selectedPrefix s.positive s.mass s.remaining)
    (a : ℕ) (ha : a ∈ actualSmallRosserSupport N cap w) :
    chenPrimeDivisorCount N (a * leaf.selected.prod) =
      ((a.primeFactors.card + leaf.selected.length : ℕ) : ℝ) := by
  have hsmall := actualSmallRosserSupport_smallPrimeSupportedAt N cap w ha
  have hdata := (actual_terminal_metadata delta n e q om N cap w z
    c s hs R leaf hl).2
  have hb : leaf.selected.prod ≠ 0 := by
    apply List.prod_ne_zero
    intro hzero
    exact (hdata 0 hzero).1.ne_zero rfl
  have hfactor := actual_terminal_full_factor_set delta n e q om N cap w z
    c s hs R leaf hl a ha
  have hall : ∀ p ∈ (a * leaf.selected.prod).primeFactors, p ≤ N := by
    intro p hp
    rw [hfactor] at hp
    rcases Finset.mem_union.mp hp with hpa | hpr
    · have hM := Nat.primeFactors_mono
        (Nat.mem_divisors.mp ha).1
        (actualSmallPrimeProduct_ne_zero N cap w) hpa
      rw [actualSmallPrimeProduct_primeFactors] at hM
      exact (Nat.le_of_lt (mem_actualSmallPrimeFinset.mp hM).1).trans hcapN
    · have hsub := actual_terminal_selected_sublist
        delta n e q om N cap w z c s hs R leaf hl
      have hcarrier : p ∈ roughPrimeUniverse N cap w z :=
        hsub.subset (by simpa using (List.mem_toFinset.mp hpr))
      exact (Nat.le_of_lt (mem_roughPrimeUniverse.mp hcarrier).1).trans hcapN
  have hfilter : ((a * leaf.selected.prod).primeFactors.filter (fun p => p ≤ N)) =
      (a * leaf.selected.prod).primeFactors := by
    exact Finset.filter_eq_self.mpr hall
  unfold chenPrimeDivisorCount
  rw [prefix_divisors_eq_filtered_factors N _ (mul_ne_zero hsmall.1 hb), hfilter]
  exact_mod_cast (actual_terminal_full_factor_card delta n e q om N cap w z
    c s hs R leaf hl a ha)

/-- The actual own-sixth parent continuation is a concrete instance,
including its fifth fallback. No new policy or leaf supplier is assumed. -/
theorem original_sixth_terminal_factor_card
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z : ℝ) (c : Cell) (s : FirstExitDepthState ℕ)
    (hs : s ∈ changedStates delta n e q om N cap w z c)
    (leaf : FirstExitLeaf ℕ)
    (hl : leaf ∈ firstExitRetainedLeaves
      (ordinaryParityRosserPolicy false
        ((N : ℝ) ^ actualParent n e q om (N : ℝ) s.selectedPrefix))
      (fun _ => 1) s.selectedPrefix s.positive s.mass s.remaining)
    (a : ℕ) (ha : a ∈ actualSmallRosserSupport N cap w) :
    (a * leaf.selected.prod).primeFactors.card =
      a.primeFactors.card + leaf.selected.length :=
  actual_terminal_full_factor_card delta n e q om N cap w z c s hs
    _ leaf hl a ha

/-- The SAVED eighth cap continuation has the SAME exact full-q factor
population theorem; it differs only in the genuine existing ordinary level. -/
theorem saved_eighth_terminal_factor_card
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z : ℝ) (c : Cell) (s : FirstExitDepthState ℕ)
    (hs : s ∈ changedStates delta n e q om N cap w z c)
    (leaf : FirstExitLeaf ℕ)
    (hl : leaf ∈ firstExitRetainedLeaves
      (ordinaryParityRosserPolicy false
        ((N : ℝ) ^ (finiteCap n c (point8 (N : ℝ) s.selectedPrefix) : ℝ)))
      (fun _ => 1) s.selectedPrefix s.positive s.mass s.remaining)
    (a : ℕ) (ha : a ∈ actualSmallRosserSupport N cap w) :
    (a * leaf.selected.prod).primeFactors.card =
      a.primeFactors.card + leaf.selected.length :=
  actual_terminal_full_factor_card delta n e q om N cap w z c s hs
    _ leaf hl a ha

end
end ImbalancedChen.P4AOriginalFull87ActualTerminalFactors
