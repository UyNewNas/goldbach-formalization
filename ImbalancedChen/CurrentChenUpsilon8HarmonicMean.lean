import ImbalancedChen.CurrentChenUpsilon8TrueLiMass
import ImbalancedChen.CurrentChenUpsilon9HarmonicMean

/-!
# The literal eighth logarithmic reciprocal-totient mass

The actual eighth selector is exactly the mixed affine region
x0 < 1/3, 1/3 <= x1, x0 + 2*x1 < 1 in the original cube [417/5000,1/2).
Its weak second-prime wall is retained in every arithmetic sum. The
already proved affine sandwich supplies the actual prime-test limit.

The eighth logarithmic gap is at least 1/3. A continuous extension with
that cutoff agrees pointwise with the unmodified kernel on the actual
region. The limit below is the literal two-dimensional integral of that
unmodified kernel; no numerical enclosure or ordinary count mean is an
input or a conclusion of this leaf.
-/

namespace ImbalancedChen

noncomputable section

open Filter Topology MeasureTheory Set
open scoped BigOperators
open Classical

def currentChenUpsilon8HarmonicRegion : Set (Fin 2 → ℝ) :=
  {x | x 0 < 1 / 3 ∧ 1 / 3 ≤ x 1 ∧ x 0 + 2 * x 1 < 1}

def currentChenUpsilon8HarmonicBounds : Fin 3 → ℝ := ![1 / 3, -(1 / 3), 1]

theorem measurableSet_currentChenUpsilon8HarmonicRegion :
    MeasurableSet currentChenUpsilon8HarmonicRegion := by
  exact (measurableSet_lt (continuous_apply 0).measurable measurable_const).inter
    ((measurableSet_le measurable_const (continuous_apply 1).measurable).inter
      (measurableSet_lt
        ((continuous_apply 0).add (continuous_const.mul (continuous_apply 1))).measurable
        measurable_const))

private theorem currentChenUpsilon8HarmonicRegion_sandwich :
    primeAffineGateRegion currentChenUpsilon9HarmonicForms
        currentChenUpsilon8HarmonicBounds ⊆ currentChenUpsilon8HarmonicRegion ∧
      ∀ x ∈ currentChenUpsilon8HarmonicRegion, ∀ j,
        currentChenUpsilon9HarmonicForms j x ≤ currentChenUpsilon8HarmonicBounds j := by
  constructor
  · intro x hx
    have h0 := hx (0 : Fin 3)
    have h1 := hx (1 : Fin 3)
    have h2 := hx (2 : Fin 3)
    change x 0 < 1 / 3 at h0
    change -x 1 < -(1 / 3 : ℝ) at h1
    change x 0 + 2 * x 1 < 1 at h2
    exact ⟨h0, by linarith only [h1], h2⟩
  · intro x hx j
    change x 0 < 1 / 3 ∧ 1 / 3 ≤ x 1 ∧ x 0 + 2 * x 1 < 1 at hx
    fin_cases j
    · change x 0 ≤ 1 / 3
      exact hx.1.le
    · change -x 1 ≤ -(1 / 3 : ℝ)
      linarith only [hx.2.1]
    · change x 0 + 2 * x 1 ≤ 1
      exact hx.2.2.le

/-- A continuous ambient extension using the actual eighth gap bound. -/
def currentChenUpsilon8HarmonicKernel (x : Fin 2 → ℝ) : ℝ :=
  1 / max (1 / 3 : ℝ) (1 - x 0 - x 1)

theorem continuous_currentChenUpsilon8HarmonicKernel :
    Continuous currentChenUpsilon8HarmonicKernel := by
  apply continuous_const.div
    (continuous_const.max ((continuous_const.sub (continuous_apply 0)).sub (continuous_apply 1)))
  intro x
  exact ne_of_gt (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 3) (le_max_left _ _))

theorem currentChenUpsilon8HarmonicKernel_eq {x : Fin 2 → ℝ}
    (hx : x ∈ currentChenUpsilon8HarmonicRegion) :
    currentChenUpsilon8HarmonicKernel x = 1 / (1 - x 0 - x 1) := by
  unfold currentChenUpsilon8HarmonicKernel
  change x 0 < 1 / 3 ∧ 1 / 3 ≤ x 1 ∧ x 0 + 2 * x 1 < 1 at hx
  have hgap : (1 / 3 : ℝ) ≤ 1 - x 0 - x 1 := by
    linarith only [hx.1, hx.2.2]
  rw [max_eq_right hgap]

private theorem currentChenUpsilon8_log_region_iff {N : ℕ} (hN : 2 ≤ N)
    (p : Fin 2 → ℕ) (hp : ∀ i, 0 < p i) :
    actualPrimeTupleLog N p ∈ currentChenUpsilon8HarmonicRegion ↔
      (p 0 : ℝ) < (N : ℝ) ^ (1 / 3 : ℝ) ∧
        (N : ℝ) ^ (1 / 3 : ℝ) ≤ (p 1 : ℝ) ∧
          (p 1 : ℝ) < Real.sqrt ((N : ℝ) / (p 0 : ℝ)) := by
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hNn : 1 < N := by omega
  have hfirst : actualPrimeTupleLog N p 0 < (1 / 3 : ℝ) ↔
      (p 0 : ℝ) < (N : ℝ) ^ (1 / 3 : ℝ) := by
    rw [← Real.rpow_lt_rpow_left_iff hNr, actualPrimeTupleLog_rpow hNn p hp]
  have hsecond : (1 / 3 : ℝ) ≤ actualPrimeTupleLog N p 1 ↔
      (N : ℝ) ^ (1 / 3 : ℝ) ≤ (p 1 : ℝ) := by
    rw [← Real.rpow_le_rpow_left_iff hNr, actualPrimeTupleLog_rpow hNn p hp]
  have hcap := currentChenUpsilon9_sqrt_log_iff hN (hp 0) (hp 1)
  change ((actualPrimeTupleLog N p 0 < 1 / 3) ∧
      1 / 3 ≤ actualPrimeTupleLog N p 1 ∧
        actualPrimeTupleLog N p 0 + 2 * actualPrimeTupleLog N p 1 < 1) ↔ _
  exact and_congr hfirst (and_congr hsecond hcap.symm)

/-- Exact dictionary with the original eighth endpoints and target masks. -/
theorem currentChenUpsilon8_tuple_mem_iff {N : ℕ} (hN : 2 ≤ N) (p : Fin 2 → ℕ) :
    (p 0, p 1) ∈ chenY8PrimeSelector N ((N : ℝ) ^ (417 / 5000 : ℝ))
        ((N : ℝ) ^ (1 / 3 : ℝ)) ↔
      p ∈ (actualPrimeBoxTuples N (fun _ : Fin 2 => (417 / 5000 : ℝ))
        (fun _ => (1 / 2 : ℝ))).filter
          (fun p => actualPrimeTupleLog N p ∈ currentChenUpsilon8HarmonicRegion) := by
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hNp : (0 : ℝ) < N := zero_lt_one.trans hNr
  have hpow : (N : ℝ) ^ (1 / 2 : ℝ) < N := by
    simpa only [Real.rpow_one] using
      Real.rpow_lt_rpow_of_exponent_lt hNr (by norm_num : (1 / 2 : ℝ) < 1)
  constructor
  · intro ht
    obtain ⟨hc, hH, hfirst, hsecond, hcap⟩ := Finset.mem_filter.mp ht
    obtain ⟨hc0, hc1⟩ := Finset.mem_product.mp hc
    have hp0 := mem_chenAdditivePrimeCarrier.mp hc0
    have hp1 := mem_chenAdditivePrimeCarrier.mp hc1
    have hpos : ∀ i, 0 < p i := by
      intro i
      fin_cases i
      · exact hp0.2.1.pos
      · exact hp1.2.1.pos
    have hp0One : (1 : ℝ) ≤ p 0 := by exact_mod_cast hp0.2.1.one_le
    have hupper0 : (p 0 : ℝ) < (N : ℝ) ^ (1 / 2 : ℝ) :=
      hfirst.trans_le (Real.rpow_le_rpow_of_exponent_le hNr.le (by norm_num))
    have hupper1 : (p 1 : ℝ) < (N : ℝ) ^ (1 / 2 : ℝ) := by
      calc
        _ < Real.sqrt ((N : ℝ) / (p 0 : ℝ)) := hcap
        _ ≤ Real.sqrt (N : ℝ) := Real.sqrt_le_sqrt (div_le_self hNp.le hp0One)
        _ = _ := Real.sqrt_eq_rpow _
    refine Finset.mem_filter.mpr ⟨mem_actualPrimeBoxTuples_iff.mpr ?_,
      (currentChenUpsilon8_log_region_iff hN p hpos).mpr ⟨hfirst, hsecond, hcap⟩⟩
    intro i
    fin_cases i
    · exact ⟨hp0.2.1, hp0.2.1.coprime_iff_not_dvd.mp hp0.2.2, hH, hupper0⟩
    · exact ⟨hp1.2.1, hp1.2.1.coprime_iff_not_dvd.mp hp1.2.2,
        (Real.rpow_le_rpow_of_exponent_le hNr.le (by norm_num)).trans hsecond, hupper1⟩
  · intro hp
    obtain ⟨hbox, hregion⟩ := Finset.mem_filter.mp hp
    have hi := mem_actualPrimeBoxTuples_iff.mp hbox
    have hpos := fun i => (hi i).1.pos
    obtain ⟨hfirst, hsecond, hcap⟩ :=
      (currentChenUpsilon8_log_region_iff hN p hpos).mp hregion
    have hcarrier (i : Fin 2) : p i ∈ chenAdditivePrimeCarrier N := by
      apply mem_chenAdditivePrimeCarrier.mpr
      refine ⟨?_, (hi i).1, (hi i).1.coprime_iff_not_dvd.mpr (hi i).2.1⟩
      exact_mod_cast (hi i).2.2.2.trans hpow
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨hcarrier 0, hcarrier 1⟩, (hi 0).2.2.1,
        hfirst, hsecond, hcap⟩

/-- Actual prime-factor separation and product injectivity pay the exact
reciprocal-totient test transport before any limit is used. -/
theorem currentChenUpsilon8LogTotientMass_eq_actualPrimeBox {N : ℕ} (hN : 2 ≤ N) :
    currentChenUpsilon8LogTotientMass N =
      actualPrimeBoxTestSum N (fun _ : Fin 2 => (417 / 5000 : ℝ)) (fun _ => (1 / 2 : ℝ))
        (currentChenUpsilon8HarmonicRegion.indicator currentChenUpsilon8HarmonicKernel) := by
  let T := (actualPrimeBoxTuples N (fun _ : Fin 2 => (417 / 5000 : ℝ))
    (fun _ => (1 / 2 : ℝ))).filter
      (fun p => actualPrimeTupleLog N p ∈ currentChenUpsilon8HarmonicRegion)
  unfold currentChenUpsilon8LogTotientMass currentChenUpsilon8PrefixProducts
  rw [Finset.sum_image (chenY8PrimeSelector_multiplier_injOn N _ _)]
  calc
    _ = ∑ p ∈ T, (∏ i, 1 / ((p i : ℝ) - 1)) *
        currentChenUpsilon8HarmonicKernel (actualPrimeTupleLog N p) := by
      refine Finset.sum_bij (fun t _ => ![t.1, t.2]) ?_ ?_ ?_ ?_
      · intro t ht
        exact (currentChenUpsilon8_tuple_mem_iff hN ![t.1, t.2]).mp ht
      · intro t _ u _ htu
        apply Prod.ext
        · simpa using congrFun htu 0
        · simpa using congrFun htu 1
      · intro p hp
        refine ⟨(p 0, p 1), (currentChenUpsilon8_tuple_mem_iff hN p).mpr hp, ?_⟩
        funext i
        fin_cases i <;> rfl
      · intro t ht
        have ht9 : t ∈ chenY9PrimeSelector N ((N : ℝ) ^ (417 / 5000 : ℝ))
            ((N : ℝ) ^ (1 / 3 : ℝ)) := ht
        obtain ⟨hp, hq, horder⟩ := chenY9PrimeSelector_ordered_prime_data ht9
        have hregion := (Finset.mem_filter.mp
          ((currentChenUpsilon8_tuple_mem_iff hN ![t.1, t.2]).mp ht)).2
        rw [currentChenUpsilon8HarmonicKernel_eq hregion,
          chen_prime_pair_totient_cast hp hq horder.ne,
          Nat.cast_mul, Real.log_mul (by exact_mod_cast hp.ne_zero) (by exact_mod_cast hq.ne_zero)]
        simp only [actualPrimeTupleLog, Fin.prod_univ_two, Matrix.cons_val_zero,
          Matrix.cons_val_one, div_eq_mul_inv, mul_inv_rev, one_mul]
        ring
    _ = _ := by
      unfold T actualPrimeBoxTestSum
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro p _
      by_cases hr : actualPrimeTupleLog N p ∈ currentChenUpsilon8HarmonicRegion
      · rw [if_pos hr, Set.indicator_of_mem hr]
      · rw [if_neg hr, Set.indicator_of_notMem hr, mul_zero]

/-- The true eighth two-dimensional integral with its unmodified kernel. -/
def currentChenUpsilon8HarmonicIntegral : ℝ :=
  ∫ x in logPrimeBox (fun _ : Fin 2 => (417 / 5000 : ℝ)) (fun _ => (1 / 2 : ℝ)) ∩
      currentChenUpsilon8HarmonicRegion,
    (1 / (1 - x 0 - x 1)) * ∏ i, 1 / x i

theorem tendsto_currentChenUpsilon8LogTotientMass :
    Tendsto currentChenUpsilon8LogTotientMass atTop (𝓝 currentChenUpsilon8HarmonicIntegral) := by
  have hlim := tendsto_actualPrimeBoxTestSum_cube_affineSandwich
    (by norm_num : (0 : ℝ) < 417 / 5000) (by norm_num : (417 / 5000 : ℝ) < 1 / 2)
    currentChenUpsilon9HarmonicForms currentChenUpsilon8HarmonicBounds
    currentChenUpsilon9HarmonicForms_ne_zero currentChenUpsilon8HarmonicRegion
    measurableSet_currentChenUpsilon8HarmonicRegion currentChenUpsilon8HarmonicRegion_sandwich.1
    currentChenUpsilon8HarmonicRegion_sandwich.2 currentChenUpsilon8HarmonicKernel
    continuous_currentChenUpsilon8HarmonicKernel.continuousOn
  have hJ : (∫ x in logPrimeBox (fun _ : Fin 2 => (417 / 5000 : ℝ))
        (fun _ => (1 / 2 : ℝ)) ∩ currentChenUpsilon8HarmonicRegion,
      currentChenUpsilon8HarmonicKernel x * ∏ i, 1 / x i) =
        currentChenUpsilon8HarmonicIntegral := by
    unfold currentChenUpsilon8HarmonicIntegral
    apply setIntegral_congr_fun
      ((measurableSet_logPrimeBox _ _).inter measurableSet_currentChenUpsilon8HarmonicRegion)
    intro x hx
    change currentChenUpsilon8HarmonicKernel x * (∏ i, 1 / x i) =
      (1 / (1 - x 0 - x 1)) * (∏ i, 1 / x i)
    rw [currentChenUpsilon8HarmonicKernel_eq hx.2]
  rw [hJ] at hlim
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with N hN
  exact (currentChenUpsilon8LogTotientMass_eq_actualPrimeBox hN).symm

end

end ImbalancedChen
