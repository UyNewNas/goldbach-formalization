import ImbalancedChen.CurrentChenPairLevelGeometry
import ImbalancedChen.ChenPairHarmonicFinite
import ImbalancedChen.ActualPrimePolyhedralTestFunctions

/-!
# The actual current fifth-selector harmonic limit

The existing actual prime-box theorem supplies the analytic limit. This
module proves the exact dictionary from the current Chen selector to its
strict ordered triangle, retaining the common target exclusion, both
half-open endpoints, and the reciprocal totient of each distinct pair.
The final test is the varying ordinary residual profile, not a fixed s.

This is a harmonic main-term limit. It is not the actual quotient count
mean or the stronger causal h248 contribution used by the manuscript.
Held source candidate: not yet compiled, kernel-replayed, or axiom-audited.
-/

namespace ImbalancedChen

noncomputable section

open Filter Topology MeasureTheory
open scoped Classical BigOperators

def currentChenPairOrderForms : Fin 1 → (Fin 2 → ℝ) →L[ℝ] ℝ :=
  fun _ =>
    (ContinuousLinearMap.proj (0 : Fin 2) : (Fin 2 → ℝ) →L[ℝ] ℝ) -
      (ContinuousLinearMap.proj (1 : Fin 2) : (Fin 2 → ℝ) →L[ℝ] ℝ)

theorem currentChenPairOrderForms_ne_zero : ∀ j, currentChenPairOrderForms j ≠ 0 := by
  intro j h
  have hh := congrArg (fun F : (Fin 2 → ℝ) →L[ℝ] ℝ => F ![1, 0]) h
  norm_num [currentChenPairOrderForms] at hh

theorem mem_currentChenPairOrderRegion (x : Fin 2 → ℝ) :
    x ∈ primeAffineGateRegion currentChenPairOrderForms (fun _ => 0) ↔ x 0 < x 1 := by
  simp [primeAffineGateRegion, currentChenPairOrderForms]

private theorem currentChenPairTuple_mem_iff {N : ℕ} (hN : 2 ≤ N) (p : Fin 2 → ℕ) :
    (p 0, p 1) ∈ chenY5PrimeSelector N ((N : ℝ) ^ (417 / 5000 : ℝ))
        ((N : ℝ) ^ (19 / 125 : ℝ)) ↔
      p ∈ (actualPrimeBoxTuples N (fun _ : Fin 2 => (417 / 5000 : ℝ))
        (fun _ => (19 / 125 : ℝ))).filter (fun p => p 0 < p 1) := by
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hupper : (N : ℝ) ^ (19 / 125 : ℝ) < N := by
    simpa only [Real.rpow_one] using
      Real.rpow_lt_rpow_of_exponent_lt hNr (by norm_num : (19 / 125 : ℝ) < 1)
  rw [chenY5PrimeSelector_eq_single_square_filter]
  constructor
  · intro hp
    obtain ⟨hprod, horder⟩ := Finset.mem_filter.mp hp
    obtain ⟨hp₀, hp₁⟩ := Finset.mem_product.mp hprod
    have h₀ := Finset.mem_filter.mp hp₀
    have h₁ := Finset.mem_filter.mp hp₁
    have hc₀ := mem_chenAdditivePrimeCarrier.mp h₀.1
    have hc₁ := mem_chenAdditivePrimeCarrier.mp h₁.1
    refine Finset.mem_filter.mpr ⟨mem_actualPrimeBoxTuples_iff.mpr ?_, horder⟩
    intro i
    fin_cases i
    · exact ⟨hc₀.2.1, hc₀.2.1.coprime_iff_not_dvd.mp hc₀.2.2, h₀.2⟩
    · exact ⟨hc₁.2.1, hc₁.2.1.coprime_iff_not_dvd.mp hc₁.2.2, h₁.2⟩
  · intro hp
    obtain ⟨hpbox, horder⟩ := Finset.mem_filter.mp hp
    have hi := mem_actualPrimeBoxTuples_iff.mp hpbox
    have hsingle (i : Fin 2) : p i ∈ chenSinglePrimeSelector N
        ((N : ℝ) ^ (417 / 5000 : ℝ)) ((N : ℝ) ^ (19 / 125 : ℝ)) := by
      refine Finset.mem_filter.mpr ⟨mem_chenAdditivePrimeCarrier.mpr ?_, (hi i).2.2⟩
      refine ⟨?_, (hi i).1, (hi i).1.coprime_iff_not_dvd.mpr (hi i).2.1⟩
      exact_mod_cast (hi i).2.2.2.trans hupper
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hsingle 0, hsingle 1⟩, horder⟩

private theorem currentChenPairLog_order_iff {N : ℕ} (hN : 2 ≤ N)
    {p : Fin 2 → ℕ}
    (hp : p ∈ actualPrimeBoxTuples N (fun _ : Fin 2 => (417 / 5000 : ℝ))
      (fun _ => (19 / 125 : ℝ))) :
    actualPrimeTupleLog N p ∈ primeAffineGateRegion currentChenPairOrderForms
      (fun _ => 0) ↔ p 0 < p 1 := by
  have hN' : 1 < N := by omega
  have hNr : (1 : ℝ) < N := by exact_mod_cast hN'
  have hpos : ∀ i, 0 < p i := fun i => (mem_actualPrimeBoxTuples_iff.mp hp i).1.pos
  rw [mem_currentChenPairOrderRegion, ← Real.rpow_lt_rpow_left_iff hNr,
    actualPrimeTupleLog_rpow hN' p hpos, actualPrimeTupleLog_rpow hN' p hpos]
  exact Nat.cast_lt

/-- Exact finite equality, including the strict diagonal deletion and the
same target-dependent prime exclusions on each side. -/
theorem currentChenUpsilon5_harmonic_eq_actualPrimeBox {N : ℕ} (hN : 2 ≤ N)
    (f : (Fin 2 → ℝ) → ℝ) :
    (∑ t ∈ chenY5PrimeSelector N ((N : ℝ) ^ (417 / 5000 : ℝ))
        ((N : ℝ) ^ (19 / 125 : ℝ)),
      f (actualPrimeTupleLog N ![t.1, t.2]) / (Nat.totient (t.1 * t.2) : ℝ)) =
    actualPrimeBoxTestSum N (fun _ : Fin 2 => (417 / 5000 : ℝ))
      (fun _ => (19 / 125 : ℝ))
      ((primeAffineGateRegion currentChenPairOrderForms (fun _ => 0)).indicator f) := by
  let T := (actualPrimeBoxTuples N (fun _ : Fin 2 => (417 / 5000 : ℝ))
    (fun _ => (19 / 125 : ℝ))).filter (fun p => p 0 < p 1)
  calc
    _ = ∑ p ∈ T, (∏ i, 1 / ((p i : ℝ) - 1)) * f (actualPrimeTupleLog N p) := by
      refine Finset.sum_bij (fun t _ => ![t.1, t.2]) ?_ ?_ ?_ ?_
      · intro t ht
        exact (currentChenPairTuple_mem_iff hN ![t.1, t.2]).mp ht
      · intro t _ht u _hu htu
        apply Prod.ext
        · simpa using congrFun htu 0
        · simpa using congrFun htu 1
      · intro p hp
        refine ⟨(p 0, p 1), (currentChenPairTuple_mem_iff hN p).mpr hp, ?_⟩
        funext i
        fin_cases i <;> rfl
      · intro t ht
        obtain ⟨htc, _, horder, _⟩ := Finset.mem_filter.mp ht
        have hp := (mem_chenAdditivePrimeCarrier.mp (Finset.mem_product.mp htc).1).2.1
        have hq := (mem_chenAdditivePrimeCarrier.mp (Finset.mem_product.mp htc).2).2.1
        rw [chen_prime_pair_totient_cast hp hq horder.ne]
        simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
          div_eq_mul_inv, mul_inv_rev, one_mul]
        ring
    _ = _ := by
      unfold T actualPrimeBoxTestSum
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro p hp
      have hgate := currentChenPairLog_order_iff hN hp
      by_cases horder : p 0 < p 1
      · rw [if_pos horder, Set.indicator_of_mem (hgate.mpr horder)]
      · rw [if_neg horder, Set.indicator_of_notMem (fun h => horder (hgate.mp h)), mul_zero]

/-- The fixed-profile limit is supplied, rather than assumed, for every
continuous test on the actual current square. The integral domain is the
strict triangle, so no unproved diagonal estimate occurs. -/
theorem tendsto_currentChenUpsilon5_harmonic_test
    (f : (Fin 2 → ℝ) → ℝ)
    (hf : ContinuousOn f (Set.univ.pi
      (fun _ : Fin 2 => Set.Icc (417 / 5000 : ℝ) (19 / 125)))) :
    Tendsto (fun N : ℕ =>
      ∑ t ∈ chenY5PrimeSelector N ((N : ℝ) ^ (417 / 5000 : ℝ))
          ((N : ℝ) ^ (19 / 125 : ℝ)),
        f (actualPrimeTupleLog N ![t.1, t.2]) / (Nat.totient (t.1 * t.2) : ℝ)) atTop
      (𝓝 (∫ x in logPrimeBox (fun _ : Fin 2 => (417 / 5000 : ℝ))
          (fun _ => (19 / 125 : ℝ)) ∩
          primeAffineGateRegion currentChenPairOrderForms (fun _ => 0),
        f x * ∏ i, 1 / x i)) := by
  have hlim := tendsto_actualPrimeBoxTestSum_cube_affineGates
    (by norm_num : (0 : ℝ) < 417 / 5000)
    (by norm_num : (417 / 5000 : ℝ) < 19 / 125)
    currentChenPairOrderForms (fun _ => 0) currentChenPairOrderForms_ne_zero f hf
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with N hN
  exact (currentChenUpsilon5_harmonic_eq_actualPrimeBox hN f).symm

def currentChenPairOrdinaryProfile (x : Fin 2 → ℝ) : ℝ :=
  ((1 / 2 : ℝ) - x 0 - x 1) / (417 / 5000)

def currentChenPairOrdinaryKernel (x : Fin 2 → ℝ) : ℝ :=
  4 * Real.log (currentChenPairOrdinaryProfile x - 1) /
    (currentChenPairOrdinaryProfile x * (417 / 5000))

theorem currentChenPairOrdinaryProfile_mem {x : Fin 2 → ℝ}
    (hx : x ∈ Set.univ.pi (fun _ : Fin 2 => Set.Icc (417 / 5000 : ℝ) (19 / 125))) :
    currentChenPairOrdinaryProfile x ∈ Set.Icc (980 / 417 : ℝ) (1666 / 417) := by
  have h₀ := hx 0 (Set.mem_univ _)
  have h₁ := hx 1 (Set.mem_univ _)
  unfold currentChenPairOrdinaryProfile
  constructor <;> norm_num <;> linarith [h₀.1, h₀.2, h₁.1, h₁.2]

theorem continuousOn_currentChenPairOrdinaryKernel :
    ContinuousOn currentChenPairOrdinaryKernel
      (Set.univ.pi (fun _ : Fin 2 => Set.Icc (417 / 5000 : ℝ) (19 / 125))) := by
  have hs : Continuous currentChenPairOrdinaryProfile := by
    unfold currentChenPairOrdinaryProfile
    fun_prop
  have hspos : ∀ x ∈ Set.univ.pi
      (fun _ : Fin 2 => Set.Icc (417 / 5000 : ℝ) (19 / 125)),
      1 < currentChenPairOrdinaryProfile x := by
    intro x hx
    have hh := (currentChenPairOrdinaryProfile_mem hx).1
    linarith
  unfold currentChenPairOrdinaryKernel
  apply (continuousOn_const.mul
    ((hs.continuousOn.sub continuousOn_const).log ?_)).div
    (hs.continuousOn.mul continuousOn_const) ?_
  · intro x hx
    exact (sub_pos.mpr (hspos x hx)).ne'
  · intro x hx
    exact mul_ne_zero (zero_lt_one.trans (hspos x hx)).ne' (by norm_num)

theorem currentChenPairOrdinaryProfile_actualLog {N : ℕ} {t : ℕ × ℕ}
    (ht : t ∈ chenY5PrimeSelector N ((N : ℝ) ^ (417 / 5000 : ℝ))
      ((N : ℝ) ^ (19 / 125 : ℝ))) :
    currentChenPairOrdinaryProfile (actualPrimeTupleLog N ![t.1, t.2]) =
      currentChenPairLogProfile N (t.1 * t.2) := by
  have htc := (Finset.mem_filter.mp ht).1
  have hp := (mem_chenAdditivePrimeCarrier.mp (Finset.mem_product.mp htc).1).2.1.pos
  have hq := (mem_chenAdditivePrimeCarrier.mp (Finset.mem_product.mp htc).2).2.1.pos
  have hpR : (t.1 : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  have hqR : (t.2 : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  simp only [currentChenPairOrdinaryProfile, actualPrimeTupleLog,
    Matrix.cons_val_zero, Matrix.cons_val_one, currentChenPairLogProfile,
    Nat.cast_mul, Real.log_mul hpR hqR, add_div]
  ring

/-- The genuine current reciprocal-totient pair sum has the variable
ordinary residual integral as its limit. There is no prime-sum, density,
error estimate, or integral convergence premise. -/
theorem tendsto_currentChenUpsilon5_ordinary_harmonic_mean :
    Tendsto (fun N : ℕ =>
      ∑ t ∈ chenY5PrimeSelector N ((N : ℝ) ^ (417 / 5000 : ℝ))
          ((N : ℝ) ^ (19 / 125 : ℝ)),
        (4 * Real.log (currentChenPairLogProfile N (t.1 * t.2) - 1) /
          (currentChenPairLogProfile N (t.1 * t.2) * (417 / 5000))) /
          (Nat.totient (t.1 * t.2) : ℝ)) atTop
      (𝓝 (∫ x in logPrimeBox (fun _ : Fin 2 => (417 / 5000 : ℝ))
          (fun _ => (19 / 125 : ℝ)) ∩
          primeAffineGateRegion currentChenPairOrderForms (fun _ => 0),
        currentChenPairOrdinaryKernel x * ∏ i, 1 / x i)) := by
  have hlim := tendsto_currentChenUpsilon5_harmonic_test
    currentChenPairOrdinaryKernel continuousOn_currentChenPairOrdinaryKernel
  apply hlim.congr'
  apply Eventually.of_forall
  intro N
  apply Finset.sum_congr rfl
  intro t ht
  simp only [currentChenPairOrdinaryKernel, currentChenPairOrdinaryProfile_actualLog ht]

end

end ImbalancedChen
