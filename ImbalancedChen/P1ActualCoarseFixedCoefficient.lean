import ImbalancedChen.P1OriginalFirstStopInheritance
import ImbalancedChen.ActualPrimePresieveSplit
import ImbalancedChen.PrimeHistoryLogCoordinates

/-!
# One fixed rough coefficient for the original coarse policy

The policy here is literally `HistoricalThirdCoarse.policy`, including its
original firstStop, its actual rough activation, and its initial-level
fallback.  It is not replaced by arbitrary historical cap data.
The nonunit support theorem recovers a real retained history and derives
its original first-prime stop, initial cube and physical power cutoff.
The unit modulus must be allowed separately: its retained history is empty.
-/

namespace ImbalancedChen.P1ActualCoarseFixedCoefficient

noncomputable section

open scoped Classical
open HistoricalThirdCoarse VariableEnvelope

def roughSupport (e chi : ℝ) (m : ℕ) (omega : ℝ) (N cap : ℕ) (w z : ℝ) :
    Finset ℕ :=
  fixedRoughSupport (policy e chi m omega (N : ℝ) false) N cap w z

def roughCoefficient (e chi : ℝ) (m : ℕ) (omega : ℝ) (N cap : ℕ) (w z : ℝ) :
    ℕ → ℝ :=
  fixedRoughCoefficient (policy e chi m omega (N : ℝ) false) N cap w z

theorem oddPolicy_eq_original (e chi : ℝ) (m : ℕ) (omega N : ℝ) :
    oddFirstExitPolicy (policy e chi m omega N false) = policy e chi m omega N := by
  funext positive history
  cases positive <;> simp [oddFirstExitPolicy, policy_even]

/-- The fixed modulus support comes from the original tree itself. -/
theorem support_eq_original_retainedModuli
    (e chi : ℝ) (m : ℕ) (omega : ℝ) (N cap : ℕ) (w z : ℝ) :
    roughSupport e chi m omega N cap w z =
      firstExitRetainedModuli (policy e chi m omega (N : ℝ))
        (roughPrimeUniverse N cap w z) := by
  unfold roughSupport fixedRoughSupport oddFirstExitRetainedModuli
    firstExitRetainedModuli oddFirstExitRetainedLeaves firstExitRootLeaves
  rw [oddPolicy_eq_original]

/-- The signed density uses exactly the coefficient that will be
evaluated on integers; the original Boolean policy is unchanged. -/
theorem density_eq_original_polynomial
    (e chi : ℝ) (m : ℕ) (omega : ℝ) (N cap : ℕ) (w z : ℝ) :
    reciprocalTotientDensity (roughSupport e chi m omega N cap w z)
        (roughCoefficient e chi m omega N cap w z) =
      firstExitRetainedPolynomial (policy e chi m omega (N : ℝ))
        (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1
        (roughPrimeUniverse N cap w z) := by
  have h := oddFirstExitRetainedPolynomial_eq_fixedRoughDensity
    (policy e chi m omega (N : ℝ) false) N cap w z
  simpa only [roughSupport, roughCoefficient, oddFirstExitRetainedPolynomial,
    oddPolicy_eq_original] using h.symm

theorem divisorSum_eq_original_polynomial
    (e chi : ℝ) (m : ℕ) (omega : ℝ) (N cap : ℕ) (w z : ℝ) (n : ℤ) :
    supportedDivisorSum (roughSupport e chi m omega N cap w z)
        (roughCoefficient e chi m omega N cap w z) n.natAbs =
      firstExitRetainedPolynomial (policy e chi m omega (N : ℝ))
        (integerDivisorIndicator n) [] true 1 (roughPrimeUniverse N cap w z) := by
  have h := oddFirstExitRetainedPolynomial_eq_fixedRoughDivisorSum
    (policy e chi m omega (N : ℝ) false) N cap w z n
  simpa only [roughSupport, roughCoefficient, oddFirstExitRetainedPolynomial,
    oddPolicy_eq_original] using h.symm

/-- One support and coefficient majorize every integer, including zero. -/
theorem divisorSum_majorant
    (e chi : ℝ) (m : ℕ) (omega : ℝ) (N cap : ℕ) (w z : ℝ)
    (hzcap : z ≤ (cap : ℝ)) (n : ℤ) :
    (if ∀ p : ℕ, (p.Prime ∧ ¬p ∣ N ∧ w ≤ (p : ℝ) ∧ (p : ℝ) < z) →
      ¬(p : ℤ) ∣ n then (1 : ℝ) else 0) ≤
      supportedDivisorSum (roughSupport e chi m omega N cap w z)
        (roughCoefficient e chi m omega N cap w z) n.natAbs := by
  exact roughIndicator_le_fixedRoughDivisorSum
    (policy e chi m omega (N : ℝ) false) N cap w z hzcap n

theorem coefficient_abs_le_one
    (e chi : ℝ) (m : ℕ) (omega : ℝ) (N cap : ℕ) (w z : ℝ) (d : ℕ) :
    |roughCoefficient e chi m omega N cap w z d| ≤ 1 := by
  exact fixedRoughCoefficient_abs_le_one
    (policy e chi m omega (N : ℝ) false) N cap w z d

/-- The unit exception in the support statement is necessary. -/
theorem coefficient_one
    (e chi : ℝ) (m : ℕ) (omega : ℝ) (N cap : ℕ) (w z : ℝ) :
    roughCoefficient e chi m omega N cap w z 1 = 1 := by
  simp only [roughCoefficient, fixedRoughCoefficient,
    oddFirstExitRetainedCoefficient_one, Int.cast_one]

theorem coefficient_nonzero_mem_support
    (e chi : ℝ) (m : ℕ) (omega : ℝ) (N cap : ℕ) (w z : ℝ) (d : ℕ)
    (hc : roughCoefficient e chi m omega N cap w z d ≠ 0) :
    d ∈ roughSupport e chi m omega N cap w z := by
  by_contra hd
  apply hc
  change ((if d ∈ roughSupport e chi m omega N cap w z then
    ArithmeticFunction.moebius d else 0 : ℤ) : ℝ) = 0
  rw [if_neg hd]
  norm_num

/-- The original coarse upper-endpoint stop is a strict physical
prime cutoff. This uses the actual logarithmic inverse at `N > 1`. -/
theorem firstStop_physical_cutoff
    (e : ℝ) (m N p : ℕ) (hN : 1 < (N : ℝ)) (hp : 0 < p)
    (hstop : firstStop e m (N : ℝ) [p]) :
    (p : ℝ) < (N : ℝ) ^ (extendedFirstStop - 4 * e) := by
  obtain ⟨_i, _hlo, hhi, hbound⟩ := hstop
  have hlog : primeHistoryLogCoordinates (N : ℝ) 1 [p] 0 <
      extendedFirstStop - 4 * e := hhi.trans_le hbound
  have hpos : ∀ q ∈ [p], 0 < q := by
    intro q hq
    have hqp : q = p := by simpa using hq
    simpa only [hqp] using hp
  have hinverse := rpow_primeHistoryLogCoordinates (N : ℝ) hN
    (by simp : [p].length = 1) hpos (0 : Fin 1)
  have hinverse' : (N : ℝ) ^ primeHistoryLogCoordinates (N : ℝ) 1 [p] 0 =
      (p : ℝ) := by
    simpa [primeHistoryTuple] using hinverse
  have hpow := (Real.rpow_lt_rpow_left_iff hN).2 hlog
  rw [hinverse'] at hpow
  exact hpow

/-- A nonunit supported modulus has a real retained leaf of the original
coarse tree. Its first selected prime retains the original stop and cube,
and obeys both the real rough carrier range and the physical first cutoff.
No stop/admissibility/valid-selection premise is supplied by the caller. -/
theorem supported_nonunit_original_history
    (e chi : ℝ) (m : ℕ) (omega : ℝ) (N cap : ℕ) (w z : ℝ)
    (hN : 1 < (N : ℝ)) (d : ℕ)
    (hd : d ∈ roughSupport e chi m omega N cap w z) (hd1 : d ≠ 1) :
    ∃ leaf : FirstExitLeaf ℕ,
      leaf ∈ firstExitRetainedLeaves (policy e chi m omega (N : ℝ))
        (fun _ => 1) [] true 1 (roughPrimeUniverse N cap w z) ∧
      leaf.selected.prod = d ∧
      ∃ p : ℕ, p.Prime ∧ p ∣ d ∧ ¬p ∣ N ∧ w ≤ (p : ℝ) ∧ (p : ℝ) < z ∧
        rosserAncestor 1 leaf.selected = [p] ∧
        firstStop e m (N : ℝ) [p] ∧
        (p : ℝ) ^ 3 < (N : ℝ) ^ initial e ∧
        (p : ℝ) < (N : ℝ) ^ (extendedFirstStop - 4 * e) := by
  rw [support_eq_original_retainedModuli] at hd
  obtain ⟨leaf, hleaf, hprod⟩ :=
    (mem_firstExitRetainedModuli (policy e chi m omega (N : ℝ))
      (roughPrimeUniverse N cap w z) d).1 hd
  have hrank : 0 < leaf.selected.length := by
    cases hs : leaf.selected with
    | nil =>
        exact False.elim (hd1 (by simpa only [hs, List.prod_nil] using hprod.symm))
    | cons q qs => simp [hs]
  obtain ⟨p, hp, hancestor, hcoord, _hadm, hstop, hcube⟩ :=
    P1OriginalFirstStopInheritance.retained_leaf_original_first_witness
      e chi m omega (N : ℝ) (fun _ => 1) (roughPrimeUniverse N cap w z)
      leaf hleaf hrank
  have hprime := mem_roughPrimeUniverse_prime hp
  have hpselected : p ∈ leaf.selected := by
    have hmem := primeHistoryTuple_mem (history := leaf.selected) rfl ⟨0, hrank⟩
    change primeHistoryTuple 1 leaf.selected 0 ∈ leaf.selected at hmem
    simpa only [hcoord] using hmem
  have hpd : p ∣ d := by
    rw [← hprod]
    exact List.dvd_prod hpselected
  exact ⟨leaf, hleaf, hprod, p, hprime, hpd,
    mem_roughPrimeUniverse_not_dvd hp, mem_roughPrimeUniverse_lower hp,
    mem_roughPrimeUniverse_upper hp, hancestor, hstop, hcube,
    firstStop_physical_cutoff e m N p hN hprime.pos hstop⟩

/-- The unit coefficient corresponds to the empty history. All other
nonzero coefficients carry an actual stopped first prime. -/
theorem nonzero_coefficient_unit_or_stopped_prime
    (e chi : ℝ) (m : ℕ) (omega : ℝ) (N cap : ℕ) (w z : ℝ)
    (hN : 1 < (N : ℝ)) (d : ℕ)
    (hc : roughCoefficient e chi m omega N cap w z d ≠ 0) :
    d = 1 ∨ ∃ p : ℕ, p.Prime ∧ p ∣ d ∧ ¬p ∣ N ∧
      firstStop e m (N : ℝ) [p] ∧
      (p : ℝ) ^ 3 < (N : ℝ) ^ initial e ∧
      (p : ℝ) < (N : ℝ) ^ (extendedFirstStop - 4 * e) := by
  by_cases hd1 : d = 1
  · exact Or.inl hd1
  · have hd := coefficient_nonzero_mem_support e chi m omega N cap w z d hc
    obtain ⟨_leaf, _hleaf, _hprod, p, hp, hpd, hpN, _hw, _hz, _hancestor,
      hstop, hcube, hcut⟩ :=
      supported_nonunit_original_history e chi m omega N cap w z hN d hd hd1
    exact Or.inr ⟨p, hp, hpd, hpN, hstop, hcube, hcut⟩

end

end ImbalancedChen.P1ActualCoarseFixedCoefficient
