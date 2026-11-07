import ImbalancedChen.CurrentChenSinglePrimeUpperDensity
import ImbalancedChen.ActualPrimeBoxTestFunctions
import ImbalancedChen.MovingWeightTransport

/-!
# Actual single-prime harmonic limits at the ordinary upper row level

The one-dimensional prime-box limit is transferred by an exact bijection
with the actual Chen selector, retaining both half-open endpoints and the
target-prime exclusions. For every fixed a<U<=1/3, the reciprocal-totient
mass is supplied by the genuine arithmetic limit. Compact continuity then
transports the logarithmic profile to the actual rounded row parameter.
There is no harmonic-limit, density or distribution hypothesis.
-/

namespace ImbalancedChen

noncomputable section

open Filter Topology MeasureTheory
open scoped BigOperators
open Classical

/-- The general true band is contained in the actual third selector. -/
theorem currentChenSinglePrime_selector_subset_Upsilon3 {N : ℕ} (hN : 1 ≤ N)
    (U : ℝ) (hUhi : U ≤ 1 / 3) :
    chenSinglePrimeSelector N ((N : ℝ) ^ (417 / 5000 : ℝ)) ((N : ℝ) ^ U) ⊆
      chenSinglePrimeSelector N ((N : ℝ) ^ (417 / 5000 : ℝ))
        ((N : ℝ) ^ (1 / 3 : ℝ)) := by
  intro p hp
  obtain ⟨hc, hlo, hhi⟩ := Finset.mem_filter.mp hp
  exact Finset.mem_filter.mpr ⟨hc, hlo,
    hhi.trans_le (Real.rpow_le_rpow_of_exponent_le
      (by exact_mod_cast hN : (1 : ℝ) ≤ N) hUhi)⟩

/-- The full actual third band has a fixed compact logarithmic profile. -/
theorem currentChenSinglePrime_profile_mem {N p : ℕ} (hN : 2 ≤ N)
    (hp : p ∈ chenSinglePrimeSelector N ((N : ℝ) ^ (417 / 5000 : ℝ))
      ((N : ℝ) ^ (1 / 3 : ℝ))) :
    currentChenPairLogProfile N p ∈ Set.Icc (2500 / 1251 : ℝ) (2083 / 417) := by
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hNp : (0 : ℝ) < N := zero_lt_one.trans hN1
  have hlogp := Real.log_pos hN1
  have hpp : (0 : ℝ) < p := by
    exact_mod_cast (Nat.zero_lt_one.trans (chenSinglePrimeSelector_sieve_data hp).1)
  obtain ⟨_hc, hlo, hhi⟩ := Finset.mem_filter.mp hp
  have hloglo := Real.log_le_log
    (Real.rpow_pos_of_pos hNp (417 / 5000)) hlo
  have hloghi := Real.log_le_log hpp hhi.le
  rw [Real.log_rpow hNp] at hloglo hloghi
  have hquotlo : (417 / 5000 : ℝ) ≤ Real.log (p : ℝ) / Real.log (N : ℝ) :=
    (le_div_iff₀ hlogp).mpr (by nlinarith only [hloglo])
  have hquothi : Real.log (p : ℝ) / Real.log (N : ℝ) ≤ (1 / 3 : ℝ) :=
    (div_le_iff₀ hlogp).mpr (by nlinarith only [hloghi])
  constructor <;> unfold currentChenPairLogProfile <;> norm_num <;>
    linarith only [hquotlo, hquothi]

/-- Rounding and the distribution-level logarithm are controlled uniformly
before selecting any prime in the actual third band. -/
theorem eventually_currentChenSinglePrime_row_profile (B epsilon : ℝ)
    (hepsilon : 0 < epsilon) :
    ∀ᶠ N : ℕ in atTop, ∀ p ∈
      chenSinglePrimeSelector N ((N : ℝ) ^ (417 / 5000 : ℝ))
        ((N : ℝ) ^ (1 / 3 : ℝ)),
      |chenQuotientRosserT B (417 / 5000) N p - currentChenPairLogProfile N p| <
        epsilon := by
  filter_upwards [eventually_chenQuotientRosserT_profile B (1 / 3) (417 / 5000)
    (by norm_num) (by norm_num) epsilon hepsilon] with N hprofile
  intro p hp
  exact hprofile p (Nat.zero_lt_one.trans (chenSinglePrimeSelector_sieve_data hp).1)
    (Finset.mem_filter.mp hp).2.2.le

/-- Actual rounded parameters remain in one compact upper-sieve interval
for the entire third band, including all smaller fixed upper endpoints. -/
theorem eventually_currentChenSinglePrime_row_interval (B : ℝ) :
    ∀ᶠ N : ℕ in atTop, ∀ p ∈
      chenSinglePrimeSelector N ((N : ℝ) ^ (417 / 5000 : ℝ))
        ((N : ℝ) ^ (1 / 3 : ℝ)),
      chenQuotientRosserT B (417 / 5000) N p ∈ Set.Icc (3 / 2 : ℝ) 5 := by
  filter_upwards [eventually_currentChenSinglePrime_row_profile B (1 / 1000) (by norm_num),
    eventually_ge_atTop (2 : ℕ)] with N hprofile hN
  intro p hp
  obtain ⟨hlo, hhi⟩ := currentChenSinglePrime_profile_mem hN hp
  obtain ⟨herrorlo, herrorhi⟩ := abs_lt.mp (hprofile p hp)
  constructor <;> linarith

private theorem currentChenSinglePrimeTuple_mem_iff {N : ℕ} (hN : 2 ≤ N)
    (U : ℝ) (hUhi : U ≤ 1 / 3) (p : Fin 1 → ℕ) :
    p 0 ∈ chenSinglePrimeSelector N ((N : ℝ) ^ (417 / 5000 : ℝ)) ((N : ℝ) ^ U) ↔
      p ∈ actualPrimeBoxTuples N (fun _ : Fin 1 => (417 / 5000 : ℝ))
        (fun _ => U) := by
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hupper : (N : ℝ) ^ U < N := by
    simpa only [Real.rpow_one] using
      Real.rpow_lt_rpow_of_exponent_lt hNr (show U < 1 by linarith only [hUhi])
  constructor
  · intro hp
    obtain ⟨hc, hlo, hhi⟩ := Finset.mem_filter.mp hp
    have hcp := mem_chenAdditivePrimeCarrier.mp hc
    apply mem_actualPrimeBoxTuples_iff.mpr
    intro i
    fin_cases i
    exact ⟨hcp.2.1, hcp.2.1.coprime_iff_not_dvd.mp hcp.2.2, hlo, hhi⟩
  · intro hp
    have hi := mem_actualPrimeBoxTuples_iff.mp hp 0
    refine Finset.mem_filter.mpr ⟨mem_chenAdditivePrimeCarrier.mpr ?_, hi.2.2⟩
    refine ⟨?_, hi.1, hi.1.coprime_iff_not_dvd.mpr hi.2.1⟩
    exact_mod_cast hi.2.2.2.trans hupper

/-- Exact one-dimensional reindexing, with phi(p)=p-1 on the true primes. -/
theorem currentChenSinglePrime_harmonic_eq_actualPrimeBox {N : ℕ} (hN : 2 ≤ N)
    (U : ℝ) (hUhi : U ≤ 1 / 3) (f : (Fin 1 → ℝ) → ℝ) :
    (∑ p ∈ chenSinglePrimeSelector N ((N : ℝ) ^ (417 / 5000 : ℝ)) ((N : ℝ) ^ U),
      (1 / (Nat.totient p : ℝ)) * f (actualPrimeTupleLog N ![p])) =
      actualPrimeBoxTestSum N (fun _ : Fin 1 => (417 / 5000 : ℝ)) (fun _ => U) f := by
  unfold actualPrimeBoxTestSum
  refine Finset.sum_bij (fun p _ => ![p]) ?_ ?_ ?_ ?_
  · intro p hp
    exact (currentChenSinglePrimeTuple_mem_iff hN U hUhi ![p]).mp hp
  · intro p _hp q _hq hpq
    simpa using congrFun hpq 0
  · intro p hp
    refine ⟨p 0, (currentChenSinglePrimeTuple_mem_iff hN U hUhi p).mpr hp, ?_⟩
    funext i
    fin_cases i
    rfl
  · intro p hp
    have hprime := (mem_chenAdditivePrimeCarrier.mp (Finset.mem_filter.mp hp).1).2.1
    rw [Nat.totient_prime hprime, Nat.cast_sub hprime.one_lt.le, Nat.cast_one]
    simp only [Fin.prod_univ_one, Matrix.cons_val_zero]

/-- Every continuous test on the true fixed one-dimensional box has its
actual target-linked reciprocal-totient prime limit. -/
theorem tendsto_currentChenSinglePrime_harmonic_test (U : ℝ)
    (hU : (417 / 5000 : ℝ) < U) (hUhi : U ≤ 1 / 3)
    (f : (Fin 1 → ℝ) → ℝ)
    (hf : ContinuousOn f (Set.univ.pi (fun _ : Fin 1 => Set.Icc (417 / 5000 : ℝ) U))) :
    Tendsto (fun N : ℕ =>
      ∑ p ∈ chenSinglePrimeSelector N ((N : ℝ) ^ (417 / 5000 : ℝ)) ((N : ℝ) ^ U),
        (1 / (Nat.totient p : ℝ)) * f (actualPrimeTupleLog N ![p])) atTop
      (𝓝 (∫ x in logPrimeBox (fun _ : Fin 1 => (417 / 5000 : ℝ)) (fun _ => U),
        f x * ∏ i, 1 / x i)) := by
  have hlim := tendsto_actualPrimeBoxTestSum_cube
    (by norm_num : (0 : ℝ) < 417 / 5000) hU f hf
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with N hN
  exact (currentChenSinglePrime_harmonic_eq_actualPrimeBox hN U hUhi f).symm

/-- The fixed canonical upper test is continuous on the whole closed box.
Its affine profile stays in the proved compact factor interval. -/
theorem continuousOn_currentChenSinglePrimeOrdinaryUpperTest
    (U : ℝ) (hUhi : U ≤ 1 / 3) :
    ContinuousOn (fun x : Fin 1 → ℝ => currentChenSinglePrimeOrdinaryUpperFactor
      (((1 / 2 : ℝ) - x 0) / (417 / 5000)))
      (Set.univ.pi (fun _ : Fin 1 => Set.Icc (417 / 5000 : ℝ) U)) := by
  apply continuousOn_currentChenSinglePrimeOrdinaryUpperFactor.comp
    (by fun_prop : ContinuousOn (fun x : Fin 1 → ℝ =>
      ((1 / 2 : ℝ) - x 0) / (417 / 5000))
      (Set.univ.pi (fun _ : Fin 1 => Set.Icc (417 / 5000 : ℝ) U)))
  intro x hx
  have hx0 := hx 0 (Set.mem_univ _)
  constructor <;> norm_num <;> linarith only [hx0.1, hx0.2, hUhi]

/-- The actual ordinary upper integral on the fixed half-open log interval. -/
def currentChenSinglePrimeOrdinaryUpperIntegral (U : ℝ) : ℝ :=
  ∫ x in logPrimeBox (fun _ : Fin 1 => (417 / 5000 : ℝ)) (fun _ => U),
    currentChenSinglePrimeOrdinaryUpperFactor
      (((1 / 2 : ℝ) - x 0) / (417 / 5000)) * (∏ i, 1 / x i)

/-- The total true reciprocal-totient mass is bounded by its own arithmetic limit. -/
theorem currentChenSinglePrime_reciprocalTotient_eventually_bounded
    (U : ℝ) (hU : (417 / 5000 : ℝ) < U) (hUhi : U ≤ 1 / 3) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ᶠ N : ℕ in atTop,
      (∑ p ∈ chenSinglePrimeSelector N ((N : ℝ) ^ (417 / 5000 : ℝ)) ((N : ℝ) ^ U),
        1 / (Nat.totient p : ℝ)) ≤ M := by
  have h := tendsto_currentChenSinglePrime_harmonic_test U hU hUhi
    (fun _ => (1 : ℝ)) continuousOn_const
  simp only [mul_one] at h
  exact exists_eventually_bounded_mass_of_tendsto h

/-- The canonical factor of the logarithmic profile has its true weighted
prime integral, with no pointwise or harmonic analytic premise. -/
theorem tendsto_currentChenSinglePrime_ordinary_harmonic
    (U : ℝ) (hU : (417 / 5000 : ℝ) < U) (hUhi : U ≤ 1 / 3) :
    Tendsto (fun N : ℕ =>
      ∑ p ∈ chenSinglePrimeSelector N ((N : ℝ) ^ (417 / 5000 : ℝ)) ((N : ℝ) ^ U),
        (1 / (Nat.totient p : ℝ)) *
          currentChenSinglePrimeOrdinaryUpperFactor (currentChenPairLogProfile N p))
      atTop (𝓝 (currentChenSinglePrimeOrdinaryUpperIntegral U)) := by
  have h := tendsto_currentChenSinglePrime_harmonic_test U hU hUhi
    (fun x : Fin 1 → ℝ => currentChenSinglePrimeOrdinaryUpperFactor
      (((1 / 2 : ℝ) - x 0) / (417 / 5000)))
    (continuousOn_currentChenSinglePrimeOrdinaryUpperTest U hUhi)
  apply h.congr'
  apply Eventually.of_forall
  intro N
  apply Finset.sum_congr rfl
  intro p hp
  simp only [actualPrimeTupleLog, Matrix.cons_val_zero, currentChenPairLogProfile]

/-- Nonnegativity is supplied by the actual nonnegative weighted prime sums. -/
theorem currentChenSinglePrimeOrdinaryUpperIntegral_nonneg
    (U : ℝ) (hU : (417 / 5000 : ℝ) < U) (hUhi : U ≤ 1 / 3) :
    0 ≤ currentChenSinglePrimeOrdinaryUpperIntegral U := by
  apply ge_of_tendsto (tendsto_currentChenSinglePrime_ordinary_harmonic U hU hUhi)
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with N hN
  apply Finset.sum_nonneg
  intro p hp
  have hp3 := currentChenSinglePrime_selector_subset_Upsilon3 (N := N) (by omega) U hUhi hp
  have hprof := currentChenSinglePrime_profile_mem hN hp3
  exact mul_nonneg (by positivity)
    (currentChenSinglePrimeOrdinaryUpperFactor_nonneg (by linarith only [hprof.1]))

/-- Compact continuity transports the true prime harmonic limit to the
same actual integer quotient levels used by the finite Rosser upper sieve. -/
theorem tendsto_currentChenSinglePrime_ordinary_moving_harmonic (B U : ℝ)
    (hU : (417 / 5000 : ℝ) < U) (hUhi : U ≤ 1 / 3) :
    Tendsto (fun N : ℕ =>
      ∑ p ∈ chenSinglePrimeSelector N ((N : ℝ) ^ (417 / 5000 : ℝ)) ((N : ℝ) ^ U),
        (1 / (Nat.totient p : ℝ)) * currentChenSinglePrimeOrdinaryUpperFactor
          (chenQuotientRosserT B (417 / 5000) N p))
      atTop (𝓝 (currentChenSinglePrimeOrdinaryUpperIntegral U)) := by
  obtain ⟨M, hM, hmass⟩ :=
    currentChenSinglePrime_reciprocalTotient_eventually_bounded U hU hUhi
  let T := fun N : ℕ =>
    chenSinglePrimeSelector N ((N : ℝ) ^ (417 / 5000 : ℝ)) ((N : ℝ) ^ U)
  let w := fun (_N : ℕ) (p : ℕ) => 1 / (Nat.totient p : ℝ)
  let x := fun N (p : ℕ) => chenQuotientRosserT B (417 / 5000) N p
  let y := fun N (p : ℕ) => currentChenPairLogProfile N p
  have hfixed : Tendsto (fun N : ℕ =>
      ∑ p ∈ T N, w N p * currentChenSinglePrimeOrdinaryUpperFactor (y N p))
      atTop (𝓝 (currentChenSinglePrimeOrdinaryUpperIntegral U)) :=
    tendsto_currentChenSinglePrime_ordinary_harmonic U hU hUhi
  apply tendsto_nonneg_weighted_comp_of_compact T w x y (Set.Icc (3 / 2 : ℝ) 5)
    currentChenSinglePrimeOrdinaryUpperFactor M (currentChenSinglePrimeOrdinaryUpperIntegral U)
    isCompact_Icc continuousOn_currentChenSinglePrimeOrdinaryUpperFactor hM
    (Eventually.of_forall (fun N p hp => by dsimp [w]; positivity)) hmass
    ?_ ?_ hfixed
  · filter_upwards [eventually_currentChenSinglePrime_row_interval B,
      eventually_ge_atTop (2 : ℕ)] with N hrow hN
    intro p hp
    have hp3 := currentChenSinglePrime_selector_subset_Upsilon3 (N := N) (by omega) U hUhi hp
    have hs := hrow p hp3
    have hprof := currentChenSinglePrime_profile_mem hN hp3
    exact ⟨hs, ⟨by dsimp [y]; linarith only [hprof.1],
      by dsimp [y]; linarith only [hprof.2]⟩⟩
  · intro delta hdelta
    filter_upwards [eventually_currentChenSinglePrime_row_profile B delta hdelta,
      eventually_ge_atTop (1 : ℕ)] with N hprofile hN
    intro p hp
    exact hprofile p (currentChenSinglePrime_selector_subset_Upsilon3 hN U hUhi hp)

end

end ImbalancedChen
