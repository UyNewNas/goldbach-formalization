import ImbalancedChen.P2LowerFiniteCellRounding
import ImbalancedChen.EvenRoughAbsoluteDensity

/-!
# The entire actual residual-modulus reciprocal-totient mass

SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The residual carrier is the COMPLETE divisor set of the actual target-deleted
rough prime product, not one selected modulus or a continuous omitted volume.
Its finite mass is exactly the Euler product. The existing named Goldbach
Mertens inverse-interval theorem gives a bound uniform over all enumeration
caps, so later prefix-wall payment may sum every residual before taking N.
-/

namespace ImbalancedChen.P2ActualResidualUniverseMass

noncomputable section
open scoped Classical BigOperators
open Filter Topology P2LowerFiniteCellRounding

/-- Literal full residual mass, including the unit divisor. -/
def mass (N cap : ℕ) (w z : ℝ) : ℝ :=
  ∑ d ∈ universe N cap w z, 1 / (Nat.totient d : ℝ)

theorem mass_nonneg (N cap : ℕ) (w z : ℝ) : 0 ≤ mass N cap w z := by
  apply Finset.sum_nonneg
  intro d _
  positivity

theorem roughProduct_eq_finsetProduct (N cap : ℕ) (w z : ℝ) :
    roughProduct N cap w z = (roughPrimeFinset N cap w z).prod id := by
  have h := List.prod_toFinset (fun p : ℕ => p) (roughPrimeUniverse_nodup N cap w z)
  simpa only [roughProduct, roughPrimeUniverse_toFinset, List.map_id] using h.symm

/-- Exact finite Euler expansion of ALL actual residual moduli. -/
theorem mass_eq_eulerProduct (N cap : ℕ) (w z : ℝ) :
    mass N cap w z =
      ∏ p ∈ roughPrimeFinset N cap w z, (1 + 1 / ((p : ℝ) - 1)) := by
  unfold mass universe
  rw [roughProduct_eq_finsetProduct]
  apply reciprocalTotient_sum_divisors_primeProduct N
  · intro p hp
    exact (mem_roughPrimeFinset.mp hp).2.1
  · intro p hp
    have h := mem_roughPrimeFinset.mp hp
    exact h.2.1.coprime_iff_not_dvd.mpr h.2.2.1

/-- The existing Mertens supplier is used at its exact finite prime set;
no final density/PP/mean estimate is introduced as a primitive premise. -/
theorem exists_mass_logRatio_bound :
    ∃ K : ℝ, 1 < K ∧ ∀ N cap : ℕ, Even N →
      ∀ w z : ℝ, 2 ≤ w → w ≤ z →
      mass N cap w z ≤ Real.log z / Real.log w * (1 + K / Real.log w) := by
  obtain ⟨K, hK, hbound⟩ :=
    MathlibNt.SieveTheory.MertensTheorem.exists_goldbach_inverse_interval_bound
  refine ⟨K, hK, ?_⟩
  intro N cap hN w z hw hwz
  rw [mass_eq_eulerProduct]
  exact (roughPrime_eulerProduct_le_inverseProduct N cap w z hN).trans
    (hbound (roughPrimeFinset N cap w z)
      (fun p hp => roughPrimeFinset_odd_of_even hN hp)
      w z hw hwz (fun p hp => (mem_roughPrimeFinset.mp hp).2.2.2))

/-- One constant and threshold control the COMPLETE residual sum at
positive fixed exponents, uniformly in every later enumeration cap. -/
theorem exists_eventual_uniform_mass_bound (omega v : ℝ)
    (homega : 0 < omega) (hov : omega < v) :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N →
      Even N → ∀ cap : ℕ,
        mass N cap ((N : ℝ) ^ omega) ((N : ℝ) ^ v) ≤ C := by
  obtain ⟨K, hK, hsupply⟩ := exists_mass_logRatio_bound
  have hKpos : 0 < K := zero_lt_one.trans hK
  have hv : 0 < v := homega.trans hov
  let C : ℝ := (v / omega) * (1 + K)
  have hC : 0 < C := by dsimp [C]; positivity
  have hpower : Tendsto (fun N : ℕ => (N : ℝ) ^ omega) atTop atTop :=
    (tendsto_rpow_atTop homega).comp tendsto_natCast_atTop_atTop
  have hlog : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨N0, hN0⟩ := eventually_atTop.mp
    ((hpower.eventually (eventually_ge_atTop (2 : ℝ))).and
      ((hlog.eventually (eventually_ge_atTop (1 / omega))).and
        (eventually_ge_atTop (2 : ℕ))))
  refine ⟨C, hC, max N0 2, le_max_right _ _, ?_⟩
  intro N hN hEven cap
  obtain ⟨hw, hlogN, hN2⟩ := hN0 N ((le_max_left _ _).trans hN)
  have hN1 : 1 < (N : ℝ) := by exact_mod_cast (show 1 < N by omega)
  have hNpos : 0 < (N : ℝ) := zero_lt_one.trans hN1
  have hlogpos : 0 < Real.log (N : ℝ) := Real.log_pos hN1
  have hden : 1 ≤ omega * Real.log (N : ℝ) := by
    have h := (div_le_iff₀ homega).mp hlogN
    nlinarith
  have hcut := Real.rpow_le_rpow_of_exponent_le hN1.le hov.le
  have h := hsupply N cap hEven _ _ hw hcut
  rw [Real.log_rpow hNpos, Real.log_rpow hNpos] at h
  have hratio : (v * Real.log (N : ℝ)) / (omega * Real.log (N : ℝ)) = v / omega := by
    field_simp [homega.ne', hlogpos.ne']
  rw [hratio] at h
  have hfrac : K / (omega * Real.log (N : ℝ)) ≤ K := by
    apply (div_le_iff₀ (by linarith : 0 < omega * Real.log (N : ℝ))).mpr
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hden hKpos.le
  exact h.trans (mul_le_mul_of_nonneg_left (add_le_add_left hfrac 1)
    (div_nonneg (homega.le.trans hov.le) homega.le))

end
end ImbalancedChen.P2ActualResidualUniverseMass
