import ImbalancedChen.CurrentChenUpsilon9TrueLiMass
import ImbalancedChen.ActualPrimeIcoCellTestFunctions
import ImbalancedChen.ChenPairHarmonicFinite

/-!
# The actual ninth reciprocal-totient logarithmic mass

The original half-open bands and the moving square-root wall are exactly
the mixed affine region x0<d, d<=x1, x0+2*x1<1 on the common cube [h,1/2).
The weak second-prime wall remains in the arithmetic sum.  The proved
pointwise affine sandwich handles its atoms, before null walls are used
only for the continuous integral.

A continuous positive extension of 1/(1-x0-x1) supplies the genuine prime
test limit.  Actual prime-factor separation pays the totient product and
the already proved product injection pays reindexing.  No harmonic limit,
prime-count mean, density estimate or adopted constant is assumed.
-/

namespace ImbalancedChen

noncomputable section

open Filter Topology MeasureTheory Set
open scoped BigOperators
open Classical

def currentChenUpsilon9HarmonicRegion : Set (Fin 2 → ℝ) :=
  {x | x 0 < 59 / 250 ∧ 59 / 250 ≤ x 1 ∧ x 0 + 2 * x 1 < 1}

def currentChenUpsilon9HarmonicForms : Fin 3 → (Fin 2 → ℝ) →L[ℝ] ℝ :=
  ![ContinuousLinearMap.proj 0, -ContinuousLinearMap.proj 1,
    ContinuousLinearMap.proj 0 + (2 : ℝ) • ContinuousLinearMap.proj 1]

def currentChenUpsilon9HarmonicBounds : Fin 3 → ℝ := ![59 / 250, -(59 / 250), 1]

theorem currentChenUpsilon9HarmonicForms_ne_zero :
    ∀ j, currentChenUpsilon9HarmonicForms j ≠ 0 := by
  intro j h
  have hh := congrArg (fun F : (Fin 2 → ℝ) →L[ℝ] ℝ => F ![1, 1]) h
  fin_cases j <;> norm_num [currentChenUpsilon9HarmonicForms] at hh

theorem measurableSet_currentChenUpsilon9HarmonicRegion :
    MeasurableSet currentChenUpsilon9HarmonicRegion := by
  exact (measurableSet_lt (continuous_apply 0).measurable measurable_const).inter
    ((measurableSet_le measurable_const (continuous_apply 1).measurable).inter
      (measurableSet_lt
        ((continuous_apply 0).add (continuous_const.mul (continuous_apply 1))).measurable
        measurable_const))

private theorem currentChenUpsilon9HarmonicRegion_sandwich :
    primeAffineGateRegion currentChenUpsilon9HarmonicForms
        currentChenUpsilon9HarmonicBounds ⊆ currentChenUpsilon9HarmonicRegion ∧
      ∀ x ∈ currentChenUpsilon9HarmonicRegion, ∀ j,
        currentChenUpsilon9HarmonicForms j x ≤ currentChenUpsilon9HarmonicBounds j := by
  constructor
  · intro x hx
    have h0 := hx (0 : Fin 3)
    have h1 := hx (1 : Fin 3)
    have h2 := hx (2 : Fin 3)
    change x 0 < 59 / 250 at h0
    change -x 1 < -(59 / 250 : ℝ) at h1
    change x 0 + 2 * x 1 < 1 at h2
    exact ⟨h0, by linarith only [h1], h2⟩
  · intro x hx j
    change x 0 < 59 / 250 ∧ 59 / 250 ≤ x 1 ∧ x 0 + 2 * x 1 < 1 at hx
    fin_cases j
    · change x 0 ≤ 59 / 250
      exact hx.1.le
    · change -x 1 ≤ -(59 / 250 : ℝ)
      linarith only [hx.2.1]
    · change x 0 + 2 * x 1 ≤ 1
      exact hx.2.2.le

/-- This extension is continuous on the whole ambient space.  The actual
region forces its maximum to equal the unmodified logarithmic gap. -/
def currentChenUpsilon9HarmonicKernel (x : Fin 2 → ℝ) : ℝ :=
  1 / max (191 / 500 : ℝ) (1 - x 0 - x 1)

theorem continuous_currentChenUpsilon9HarmonicKernel :
    Continuous currentChenUpsilon9HarmonicKernel := by
  apply continuous_const.div
    (continuous_const.max ((continuous_const.sub (continuous_apply 0)).sub (continuous_apply 1)))
  intro x
  exact ne_of_gt (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 191 / 500) (le_max_left _ _))

theorem currentChenUpsilon9HarmonicKernel_eq {x : Fin 2 → ℝ}
    (hx : x ∈ currentChenUpsilon9HarmonicRegion) :
    currentChenUpsilon9HarmonicKernel x = 1 / (1 - x 0 - x 1) := by
  unfold currentChenUpsilon9HarmonicKernel
  change x 0 < 59 / 250 ∧ 59 / 250 ≤ x 1 ∧ x 0 + 2 * x 1 < 1 at hx
  have hgap : (191 / 500 : ℝ) ≤ 1 - x 0 - x 1 := by
    linarith only [hx.1, hx.2.2]
  rw [max_eq_right hgap]

/-- The original moving square-root cutoff is equivalent to the affine
logarithmic wall on the actual positive prime coordinates. -/
theorem currentChenUpsilon9_sqrt_log_iff {N a b : ℕ}
    (hN : 2 ≤ N) (ha : 0 < a) (hb : 0 < b) :
    (b : ℝ) < Real.sqrt ((N : ℝ) / (a : ℝ)) ↔
      Real.log (a : ℝ) / Real.log (N : ℝ) +
        2 * (Real.log (b : ℝ) / Real.log (N : ℝ)) < 1 := by
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hNp : (0 : ℝ) < N := zero_lt_one.trans hNr
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hlog := Real.log_pos hNr
  rw [← Real.log_lt_log_iff hbR (Real.sqrt_pos.mpr (div_pos hNp haR)),
    Real.log_sqrt (div_nonneg hNp.le haR.le), Real.log_div hNp.ne' haR.ne']
  rw [show Real.log (a : ℝ) / Real.log (N : ℝ) +
      2 * (Real.log (b : ℝ) / Real.log (N : ℝ)) =
        (Real.log (a : ℝ) + 2 * Real.log (b : ℝ)) / Real.log (N : ℝ) by ring,
    div_lt_iff₀ hlog, one_mul]
  constructor <;> intro h <;> linarith only [h]

private theorem currentChenUpsilon9_log_region_iff {N : ℕ} (hN : 2 ≤ N)
    (p : Fin 2 → ℕ) (hp : ∀ i, 0 < p i) :
    actualPrimeTupleLog N p ∈ currentChenUpsilon9HarmonicRegion ↔
      (p 0 : ℝ) < (N : ℝ) ^ (59 / 250 : ℝ) ∧
        (N : ℝ) ^ (59 / 250 : ℝ) ≤ (p 1 : ℝ) ∧
          (p 1 : ℝ) < Real.sqrt ((N : ℝ) / (p 0 : ℝ)) := by
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hNn : 1 < N := by omega
  have hfirst : actualPrimeTupleLog N p 0 < (59 / 250 : ℝ) ↔
      (p 0 : ℝ) < (N : ℝ) ^ (59 / 250 : ℝ) := by
    rw [← Real.rpow_lt_rpow_left_iff hNr, actualPrimeTupleLog_rpow hNn p hp]
  have hsecond : (59 / 250 : ℝ) ≤ actualPrimeTupleLog N p 1 ↔
      (N : ℝ) ^ (59 / 250 : ℝ) ≤ (p 1 : ℝ) := by
    rw [← Real.rpow_le_rpow_left_iff hNr, actualPrimeTupleLog_rpow hNn p hp]
  have hcap := currentChenUpsilon9_sqrt_log_iff hN (hp 0) (hp 1)
  change ((actualPrimeTupleLog N p 0 < 59 / 250) ∧
      59 / 250 ≤ actualPrimeTupleLog N p 1 ∧
        actualPrimeTupleLog N p 0 + 2 * actualPrimeTupleLog N p 1 < 1) ↔ _
  exact and_congr hfirst (and_congr hsecond hcap.symm)

/-- Exact dictionary between the actual selector and the actual cube with
its mixed walls.  Both target-prime exclusions and all endpoints persist. -/
theorem currentChenUpsilon9_tuple_mem_iff {N : ℕ} (hN : 2 ≤ N) (p : Fin 2 → ℕ) :
    (p 0, p 1) ∈ chenY9PrimeSelector N ((N : ℝ) ^ (19 / 125 : ℝ))
        ((N : ℝ) ^ (59 / 250 : ℝ)) ↔
      p ∈ (actualPrimeBoxTuples N (fun _ : Fin 2 => (19 / 125 : ℝ))
        (fun _ => (1 / 2 : ℝ))).filter
          (fun p => actualPrimeTupleLog N p ∈ currentChenUpsilon9HarmonicRegion) := by
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
      (currentChenUpsilon9_log_region_iff hN p hpos).mpr ⟨hfirst, hsecond, hcap⟩⟩
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
      (currentChenUpsilon9_log_region_iff hN p hpos).mp hregion
    have hcarrier (i : Fin 2) : p i ∈ chenAdditivePrimeCarrier N := by
      apply mem_chenAdditivePrimeCarrier.mpr
      refine ⟨?_, (hi i).1, (hi i).1.coprime_iff_not_dvd.mpr (hi i).2.1⟩
      exact_mod_cast (hi i).2.2.2.trans hpow
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨hcarrier 0, hcarrier 1⟩, (hi 0).2.2.1,
        hfirst, hsecond, hcap⟩

/-- The product-image mass is the same actual prime-box test sum.  The
proved prime-factor injection is used before any analytic limit. -/
theorem currentChenUpsilon9LogTotientMass_eq_actualPrimeBox {N : ℕ} (hN : 2 ≤ N) :
    currentChenUpsilon9LogTotientMass N =
      actualPrimeBoxTestSum N (fun _ : Fin 2 => (19 / 125 : ℝ)) (fun _ => (1 / 2 : ℝ))
        (currentChenUpsilon9HarmonicRegion.indicator currentChenUpsilon9HarmonicKernel) := by
  let T := (actualPrimeBoxTuples N (fun _ : Fin 2 => (19 / 125 : ℝ))
    (fun _ => (1 / 2 : ℝ))).filter
      (fun p => actualPrimeTupleLog N p ∈ currentChenUpsilon9HarmonicRegion)
  unfold currentChenUpsilon9LogTotientMass currentChenUpsilon9PrefixProducts
  rw [Finset.sum_image (chenY9PrimeSelector_multiplier_injOn N _ _)]
  calc
    _ = ∑ p ∈ T, (∏ i, 1 / ((p i : ℝ) - 1)) *
        currentChenUpsilon9HarmonicKernel (actualPrimeTupleLog N p) := by
      refine Finset.sum_bij (fun t _ => ![t.1, t.2]) ?_ ?_ ?_ ?_
      · intro t ht
        exact (currentChenUpsilon9_tuple_mem_iff hN ![t.1, t.2]).mp ht
      · intro t _ u _ htu
        apply Prod.ext
        · simpa using congrFun htu 0
        · simpa using congrFun htu 1
      · intro p hp
        refine ⟨(p 0, p 1), (currentChenUpsilon9_tuple_mem_iff hN p).mpr hp, ?_⟩
        funext i
        fin_cases i <;> rfl
      · intro t ht
        obtain ⟨hp, hq, horder⟩ := chenY9PrimeSelector_ordered_prime_data ht
        have hregion := (Finset.mem_filter.mp
          ((currentChenUpsilon9_tuple_mem_iff hN ![t.1, t.2]).mp ht)).2
        rw [currentChenUpsilon9HarmonicKernel_eq hregion,
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
      by_cases hr : actualPrimeTupleLog N p ∈ currentChenUpsilon9HarmonicRegion
      · rw [if_pos hr, Set.indicator_of_mem hr]
      · rw [if_neg hr, Set.indicator_of_notMem hr, mul_zero]

/-- The true harmonic integral, before any one-dimensional integration
dictionary or numerical enclosure is applied. -/
def currentChenUpsilon9HarmonicIntegral : ℝ :=
  ∫ x in logPrimeBox (fun _ : Fin 2 => (19 / 125 : ℝ)) (fun _ => (1 / 2 : ℝ)) ∩
      currentChenUpsilon9HarmonicRegion,
    currentChenUpsilon9HarmonicKernel x * ∏ i, 1 / x i

theorem tendsto_currentChenUpsilon9LogTotientMass :
    Tendsto currentChenUpsilon9LogTotientMass atTop (𝓝 currentChenUpsilon9HarmonicIntegral) := by
  have hlim := tendsto_actualPrimeBoxTestSum_cube_affineSandwich
    (by norm_num : (0 : ℝ) < 19 / 125) (by norm_num : (19 / 125 : ℝ) < 1 / 2)
    currentChenUpsilon9HarmonicForms currentChenUpsilon9HarmonicBounds
    currentChenUpsilon9HarmonicForms_ne_zero currentChenUpsilon9HarmonicRegion
    measurableSet_currentChenUpsilon9HarmonicRegion currentChenUpsilon9HarmonicRegion_sandwich.1
    currentChenUpsilon9HarmonicRegion_sandwich.2 currentChenUpsilon9HarmonicKernel
    continuous_currentChenUpsilon9HarmonicKernel.continuousOn
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with N hN
  exact (currentChenUpsilon9LogTotientMass_eq_actualPrimeBox hN).symm

end

end ImbalancedChen
