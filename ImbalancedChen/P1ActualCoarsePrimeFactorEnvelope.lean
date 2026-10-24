import ImbalancedChen.P1ActualCoarseFixedCoefficient

/-!
# The original coarse first stop bounds every retained prime factor

The actual rough carrier is processed in decreasing order. Its earliest
selected prime is therefore the largest selected prime. The original
rank-one stop bounds every prime factor of every supported modulus.
The final support inclusion is in divisors of an explicit buffered rough
primorial; no power bound on the whole modulus is asserted.
-/

namespace ImbalancedChen.P1ActualCoarsePrimeFactorEnvelope

noncomputable section

open scoped Classical
open HistoricalThirdCoarse VariableEnvelope
open P1ActualCoarseFixedCoefficient

/-- Reverse storage does not change which selected prime is largest.
The literal first ancestor, rather than a supplied maximum, identifies it. -/
theorem selected_le_first_of_reverse_pairwise
    (history : List ℕ) (p : ℕ) (hsort : history.reverse.Pairwise (· > ·))
    (hancestor : rosserAncestor 1 history = [p])
    (q : ℕ) (hq : q ∈ history) : q ≤ p := by
  have hqrev : q ∈ history.reverse := List.mem_reverse.mpr hq
  cases hrev : history.reverse with
  | nil =>
      rw [hrev] at hqrev
      simp at hqrev
  | cons r rs =>
      have hlen : 0 < history.length := by
        have hlenrev : 0 < history.reverse.length := by rw [hrev]; simp
        simpa only [List.length_reverse] using hlenrev
      have hfirst := primeHistoryTuple_ancestor (history := history) rfl
        (by omega : 1 ≤ history.length) (0 : Fin 1)
      rw [hancestor] at hfirst
      have hpr : p = r := by simpa [primeHistoryTuple, hrev] using hfirst
      rw [hrev] at hsort hqrev
      rcases List.mem_cons.mp hqrev with hqr | hqrs
      · omega
      · have hqr : q < r := (List.pairwise_cons.mp hsort).1 q hqrs
        omega

/-- All factors of an actual retained leaf's product are bounded by its
original first selected prime. The order and prime-factor dictionary
come from the actual decreasing rough carrier. -/
theorem retained_leaf_primeFactors_le_first
    (e chi : ℝ) (m : ℕ) (omega : ℝ) (N cap : ℕ) (w z : ℝ)
    (leaf : FirstExitLeaf ℕ)
    (hleaf : leaf ∈ firstExitRetainedLeaves (policy e chi m omega (N : ℝ))
      (fun _ => 1) [] true 1 (roughPrimeUniverse N cap w z))
    (p : ℕ) (hancestor : rosserAncestor 1 leaf.selected = [p])
    (q : ℕ) (hq : q ∈ leaf.selected.prod.primeFactors) : q ≤ p := by
  have hsub := mem_firstExitRootLeaves_selected_reverse_sublist
    (policy e chi m omega (N : ℝ)) (fun _ => 1)
    (roughPrimeUniverse N cap w z) leaf hleaf
  have hsort := (roughPrimeUniverse_pairwise_gt N cap w z).sublist hsub
  have hpf := mem_firstExitRootLeaves_primeFactors_selectedProd
    (policy e chi m omega (N : ℝ)) (fun _ => 1)
    (roughPrimeUniverse N cap w z) (roughPrimeUniverse_nodup N cap w z)
    (fun _ hp => mem_roughPrimeUniverse_prime hp) leaf hleaf
  have hqselected : q ∈ leaf.selected := by
    apply List.mem_toFinset.mp
    rw [← hpf]
    exact hq
  exact selected_le_first_of_reverse_pairwise leaf.selected p hsort hancestor q hqselected

/-- Every prime factor receives the strict physical bound paid by the
original firstStop. The unit case has no prime factors. -/
theorem support_primeFactor_physical_cutoff
    (e chi : ℝ) (m : ℕ) (omega : ℝ) (N cap : ℕ) (w z : ℝ)
    (hN : 1 < (N : ℝ)) (d : ℕ)
    (hd : d ∈ roughSupport e chi m omega N cap w z)
    (q : ℕ) (hq : q ∈ d.primeFactors) :
    (q : ℝ) < (N : ℝ) ^ (extendedFirstStop - 4 * e) := by
  by_cases hd1 : d = 1
  · subst d
    simp at hq
  · obtain ⟨leaf, hleaf, hprod, p, _hp, _hpd, _hpN, _hw, _hz,
      hancestor, _hstop, _hcube, hcut⟩ :=
      supported_nonunit_original_history e chi m omega N cap w z hN d hd hd1
    have hqprod : q ∈ leaf.selected.prod.primeFactors := by
      rw [hprod]
      exact hq
    have hqp := retained_leaf_primeFactors_le_first
      e chi m omega N cap w z leaf hleaf p hancestor q hqprod
    have hqpR : (q : ℝ) ≤ (p : ℝ) := by exact_mod_cast hqp
    exact hqpR.trans_lt hcut

theorem nonzero_coefficient_primeFactor_physical_cutoff
    (e chi : ℝ) (m : ℕ) (omega : ℝ) (N cap : ℕ) (w z : ℝ)
    (hN : 1 < (N : ℝ)) (d : ℕ)
    (hc : roughCoefficient e chi m omega N cap w z d ≠ 0)
    (q : ℕ) (hq : q ∈ d.primeFactors) :
    (q : ℝ) < (N : ℝ) ^ (extendedFirstStop - 4 * e) := by
  exact support_primeFactor_physical_cutoff e chi m omega N cap w z hN d
    (coefficient_nonzero_mem_support e chi m omega N cap w z d hc) q hq

/-- The actual capped, target-deleted rough prime set with the additional
original first-stop bound. The minimum keeps both strict upper cutoffs. -/
def bufferedPrimes (e : ℝ) (N cap : ℕ) (w z : ℝ) : Finset ℕ :=
  roughPrimeFinset N cap w (min z ((N : ℝ) ^ (extendedFirstStop - 4 * e)))

def bufferedPrimorial (e : ℝ) (N cap : ℕ) (w z : ℝ) : ℕ :=
  (bufferedPrimes e N cap w z).prod id

/-- The refined support is an actual prime-factor inclusion. It preserves
the original enumeration cap, rough lower endpoint and target exclusions. -/
theorem support_primeFactors_subset_bufferedPrimes
    (e chi : ℝ) (m : ℕ) (omega : ℝ) (N cap : ℕ) (w z : ℝ)
    (hN : 1 < (N : ℝ)) (d : ℕ)
    (hd : d ∈ roughSupport e chi m omega N cap w z) :
    d.primeFactors ⊆ bufferedPrimes e N cap w z := by
  intro q hq
  have hcarrier := fixedRoughSupport_primeFactors_mem
    (policy e chi m omega (N : ℝ) false) N cap w z hd hq
  obtain ⟨hqcap, hprime, hqN, hlo, hhi⟩ := mem_roughPrimeUniverse.mp hcarrier
  have hcut := support_primeFactor_physical_cutoff
    e chi m omega N cap w z hN d hd q hq
  exact mem_roughPrimeFinset.mpr ⟨hqcap, hprime, hqN, hlo, lt_min hhi hcut⟩

theorem bufferedPrimorial_ne_zero (e : ℝ) (N cap : ℕ) (w z : ℝ) :
    bufferedPrimorial e N cap w z ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro p hp
  exact (mem_roughPrimeFinset.mp hp).2.1.ne_zero

/-- Squarefreeness and the proved prime-factor inclusion place every
actual retained modulus among divisors of the buffered rough primorial. -/
theorem support_dvd_bufferedPrimorial
    (e chi : ℝ) (m : ℕ) (omega : ℝ) (N cap : ℕ) (w z : ℝ)
    (hN : 1 < (N : ℝ)) (d : ℕ)
    (hd : d ∈ roughSupport e chi m omega N cap w z) :
    d ∣ bufferedPrimorial e N cap w z := by
  have hsq := fixedRoughSupport_squarefree
    (policy e chi m omega (N : ℝ) false) N cap w z hd
  rw [← Nat.prod_primeFactors_of_squarefree hsq]
  exact Finset.prod_dvd_prod_of_subset _ _ id
    (support_primeFactors_subset_bufferedPrimes e chi m omega N cap w z hN d hd)

theorem support_subset_bufferedPrimorial_divisors
    (e chi : ℝ) (m : ℕ) (omega : ℝ) (N cap : ℕ) (w z : ℝ)
    (hN : 1 < (N : ℝ)) :
    roughSupport e chi m omega N cap w z ⊆
      (bufferedPrimorial e N cap w z).divisors := by
  intro d hd
  exact Nat.mem_divisors.mpr
    ⟨support_dvd_bufferedPrimorial e chi m omega N cap w z hN d hd,
      bufferedPrimorial_ne_zero e N cap w z⟩

/-- Nonzero original coefficients lie on the refined finite divisor
carrier, using the original first stop rather than only the rough `z`. -/
theorem nonzero_coefficient_mem_bufferedPrimorial_divisors
    (e chi : ℝ) (m : ℕ) (omega : ℝ) (N cap : ℕ) (w z : ℝ)
    (hN : 1 < (N : ℝ)) (d : ℕ)
    (hc : roughCoefficient e chi m omega N cap w z d ≠ 0) :
    d ∈ (bufferedPrimorial e N cap w z).divisors := by
  exact support_subset_bufferedPrimorial_divisors e chi m omega N cap w z hN
    (coefficient_nonzero_mem_support e chi m omega N cap w z d hc)

theorem coefficient_zero_off_bufferedPrimorial_divisors
    (e chi : ℝ) (m : ℕ) (omega : ℝ) (N cap : ℕ) (w z : ℝ)
    (hN : 1 < (N : ℝ)) (d : ℕ)
    (hd : d ∉ (bufferedPrimorial e N cap w z).divisors) :
    roughCoefficient e chi m omega N cap w z d = 0 := by
  by_contra hc
  exact hd (nonzero_coefficient_mem_bufferedPrimorial_divisors
    e chi m omega N cap w z hN d hc)

end

end ImbalancedChen.P1ActualCoarsePrimeFactorEnvelope
