import ImbalancedChen.ActualPrimeBoxTestFunctions
import ImbalancedChen.AffinePrimeGates

/-!
# Actual prime tuples restricted by finite affine gates

The prime carrier retains exclusion of the target's prime factors. Its
nonnegative reciprocal-prime weights allow continuous ramps to control
signed tests. Proper affine walls are proved null, and dominated
convergence pays the limiting ramp error. No arithmetic convergence or
null-wall premise is required from the caller.
-/

namespace ImbalancedChen

noncomputable section

open scoped Classical BigOperators Topology
open MeasureTheory Filter Set

private theorem cube_logDensity_nonneg {d : ℕ} {a b : ℝ} (ha : 0 < a)
    {x : Fin d → ℝ} (hx : x ∈ logPrimeBox (fun _ => a) (fun _ => b)) :
    0 ≤ ∏ i, 1 / x i :=
  Finset.prod_nonneg (fun i _ => (one_div_pos.mpr (ha.trans_le (mem_logPrimeBox.mp hx i).1)).le)

private theorem integral_cube_gate_indicator {d r : ℕ} (a b : ℝ)
    (L : Fin r → (Fin d → ℝ) →L[ℝ] ℝ) (c : Fin r → ℝ)
    (f : (Fin d → ℝ) → ℝ) :
    (∫ x in logPrimeBox (fun _ : Fin d => a) (fun _ => b),
      (primeAffineGateRegion L c).indicator f x * ∏ i, 1 / x i) =
    ∫ x in logPrimeBox (fun _ : Fin d => a) (fun _ => b) ∩ primeAffineGateRegion L c,
      f x * ∏ i, 1 / x i := by
  have heq : (fun x => (primeAffineGateRegion L c).indicator f x * ∏ i, 1 / x i) =
      (primeAffineGateRegion L c).indicator (fun x => f x * ∏ i, 1 / x i) := by
    funext x
    by_cases hx : x ∈ primeAffineGateRegion L c <;> simp [hx]
  rw [heq, setIntegral_indicator (measurableSet_primeAffineGateRegion L c)]

/-- Each continuous ramp converges in the true integral on the cube;
the affine walls are removed by a proved zero-volume theorem. -/
theorem tendsto_integral_affinePrimeGateRamp {d r : ℕ} {a b : ℝ}
    (ha : 0 < a)
    (L : Fin r → (Fin d → ℝ) →L[ℝ] ℝ) (c : Fin r → ℝ) (hL : ∀ j, L j ≠ 0)
    (f : (Fin d → ℝ) → ℝ)
    (hf : ContinuousOn f (Set.univ.pi (fun _ : Fin d => Set.Icc a b))) (upper : Bool) :
    Tendsto (fun m => ∫ x in logPrimeBox (fun _ : Fin d => a) (fun _ => b),
      (f x * affinePrimeGateRamp L c upper m x) * ∏ i, 1 / x i) atTop
      (𝓝 (∫ x in logPrimeBox (fun _ : Fin d => a) (fun _ => b) ∩ primeAffineGateRegion L c,
        f x * ∏ i, 1 / x i)) := by
  have hbound := integrableOn_logPrimeBox_test_cube ha (fun x => |f x|) hf.abs
  have hlim := tendsto_integral_of_dominated_convergence
    (μ := volume.restrict (logPrimeBox (fun _ : Fin d => a) (fun _ => b)))
    (fun x => |f x| * ∏ i, 1 / x i)
    (fun m => (integrableOn_logPrimeBox_test_cube ha
      (fun x => f x * affinePrimeGateRamp L c upper m x)
      (hf.mul (continuous_affinePrimeGateRamp L c upper m).continuousOn)).aestronglyMeasurable)
    hbound
    (fun m => by
      filter_upwards [ae_restrict_mem (measurableSet_logPrimeBox
        (fun _ : Fin d => a) (fun _ => b))] with x hx
      have hd := cube_logDensity_nonneg ha hx
      have hr := affinePrimeGateRamp_bounds L c upper m x
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hr.1, abs_of_nonneg hd]
      exact mul_le_mul_of_nonneg_right
        (by simpa using mul_le_mul_of_nonneg_left hr.2 (abs_nonneg (f x))) hd)
    (show ∀ᵐ x ∂volume.restrict (logPrimeBox (fun _ : Fin d => a) (fun _ => b)),
        Tendsto (fun m => (f x * affinePrimeGateRamp L c upper m x) * ∏ i, 1 / x i)
          atTop (𝓝 ((primeAffineGateRegion L c).indicator f x * ∏ i, 1 / x i)) from by
      filter_upwards [ae_restrict_of_ae (ae_primeAffineGate_no_wall L c hL)] with x hx
      have ht := ((tendsto_affinePrimeGateRamp L c upper x hx).const_mul (f x)).mul_const
        (∏ i, 1 / x i)
      have heq : f x * (primeAffineGateRegion L c).indicator (fun _ => (1 : ℝ)) x =
          (primeAffineGateRegion L c).indicator f x := by
        by_cases hx' : x ∈ primeAffineGateRegion L c <;> simp [hx']
      simpa only [heq] using ht)
  simpa only [integral_cube_gate_indicator] using hlim

/-- The gap between the two continuous ramps has vanishing weighted
Lebesgue integral, including for an absolute value of a signed test. -/
theorem tendsto_integral_affinePrimeGateRamp_gap {d r : ℕ} {a b : ℝ}
    (ha : 0 < a)
    (L : Fin r → (Fin d → ℝ) →L[ℝ] ℝ) (c : Fin r → ℝ) (hL : ∀ j, L j ≠ 0)
    (f : (Fin d → ℝ) → ℝ)
    (hf : ContinuousOn f (Set.univ.pi (fun _ : Fin d => Set.Icc a b))) :
    Tendsto (fun m => ∫ x in logPrimeBox (fun _ : Fin d => a) (fun _ => b),
      (|f x| * (affinePrimeGateRamp L c true m x - affinePrimeGateRamp L c false m x)) *
        ∏ i, 1 / x i) atTop (𝓝 0) := by
  have ht := (tendsto_integral_affinePrimeGateRamp ha L c hL _ hf.abs true).sub
    (tendsto_integral_affinePrimeGateRamp ha L c hL _ hf.abs false)
  simp only [sub_self] at ht
  convert ht using 1
  funext m
  calc
    _ = ∫ x in logPrimeBox (fun _ : Fin d => a) (fun _ => b),
        (|f x| * affinePrimeGateRamp L c true m x) * (∏ i, 1 / x i) -
          (|f x| * affinePrimeGateRamp L c false m x) * (∏ i, 1 / x i) :=
      integral_congr_ae (Eventually.of_forall (fun x => by ring))
    _ = _ := integral_sub
      (integrableOn_logPrimeBox_test_cube ha (fun x => |f x| * affinePrimeGateRamp L c true m x)
        (hf.abs.mul (continuous_affinePrimeGateRamp L c true m).continuousOn))
      (integrableOn_logPrimeBox_test_cube ha (fun x => |f x| * affinePrimeGateRamp L c false m x)
        (hf.abs.mul (continuous_affinePrimeGateRamp L c false m).continuousOn))

/-- The finite arithmetic error is paid by the same actual prime weights,
without any sign assumption on the test function. -/
theorem actualPrimeBoxTestSum_affineGateRamp_error {d r : ℕ} (N : ℕ)
    (a b : Fin d → ℝ)
    (L : Fin r → (Fin d → ℝ) →L[ℝ] ℝ) (c : Fin r → ℝ) (m : ℕ)
    (f : (Fin d → ℝ) → ℝ) :
    |actualPrimeBoxTestSum N a b ((primeAffineGateRegion L c).indicator f) -
      actualPrimeBoxTestSum N a b (fun x => f x * affinePrimeGateRamp L c false m x)| ≤
    actualPrimeBoxTestSum N a b (fun x =>
      |f x| * (affinePrimeGateRamp L c true m x - affinePrimeGateRamp L c false m x)) := by
  unfold actualPrimeBoxTestSum
  rw [← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro p hp
  rw [← mul_sub, abs_mul, abs_of_nonneg (actualPrimeBoxWeight_nonneg hp)]
  exact mul_le_mul_of_nonneg_left (affinePrimeGateRamp_test_error L c m f _)
    (actualPrimeBoxWeight_nonneg hp)

/-- Actual target-linked prime tuples restricted by finitely many strict
nondegenerate affine gates converge to the genuine region integral.
The test may have either sign; empty gate families and dimension zero are
not excluded. No limit or null-boundary hypothesis occurs. -/
theorem tendsto_actualPrimeBoxTestSum_cube_affineGates {d r : ℕ} {a b : ℝ}
    (ha : 0 < a) (hab : a < b)
    (L : Fin r → (Fin d → ℝ) →L[ℝ] ℝ) (c : Fin r → ℝ) (hL : ∀ j, L j ≠ 0)
    (f : (Fin d → ℝ) → ℝ)
    (hf : ContinuousOn f (Set.univ.pi (fun _ : Fin d => Set.Icc a b))) :
    Tendsto (fun N : ℕ => actualPrimeBoxTestSum N (fun _ : Fin d => a) (fun _ => b)
      ((primeAffineGateRegion L c).indicator f)) atTop
      (𝓝 (∫ x in logPrimeBox (fun _ : Fin d => a) (fun _ => b) ∩ primeAffineGateRegion L c,
        f x * ∏ i, 1 / x i)) := by
  rw [Metric.tendsto_nhds]
  intro epsilon hepsilon
  let I := ∫ x in logPrimeBox (fun _ : Fin d => a) (fun _ => b) ∩ primeAffineGateRegion L c,
    f x * ∏ i, 1 / x i
  let low (m : ℕ) (x : Fin d → ℝ) := f x * affinePrimeGateRamp L c false m x
  let gap (m : ℕ) (x : Fin d → ℝ) :=
    |f x| * (affinePrimeGateRamp L c true m x - affinePrimeGateRamp L c false m x)
  let J (m : ℕ) := ∫ x in logPrimeBox (fun _ : Fin d => a) (fun _ => b), low m x * ∏ i, 1 / x i
  let E (m : ℕ) := ∫ x in logPrimeBox (fun _ : Fin d => a) (fun _ => b), gap m x * ∏ i, 1 / x i
  have hJ : ∀ᶠ m : ℕ in atTop, |J m - I| < epsilon / 4 := by
    simpa only [Real.dist_eq] using Metric.tendsto_nhds.mp
      (tendsto_integral_affinePrimeGateRamp ha L c hL f hf false) (epsilon / 4) (by positivity)
  have hE : ∀ᶠ m : ℕ in atTop, E m < epsilon / 4 :=
    (tendsto_integral_affinePrimeGateRamp_gap ha L c hL f hf).eventually
      (gt_mem_nhds (by positivity : (0 : ℝ) < epsilon / 4))
  obtain ⟨m, hmJ, hmE⟩ := (hJ.and hE).exists
  have hlow : ContinuousOn (low m) (Set.univ.pi (fun _ : Fin d => Set.Icc a b)) :=
    hf.mul (continuous_affinePrimeGateRamp L c false m).continuousOn
  have hgap : ContinuousOn (gap m) (Set.univ.pi (fun _ : Fin d => Set.Icc a b)) :=
    hf.abs.mul ((continuous_affinePrimeGateRamp L c true m).sub
      (continuous_affinePrimeGateRamp L c false m)).continuousOn
  have hNlow : ∀ᶠ N : ℕ in atTop,
      |actualPrimeBoxTestSum N (fun _ : Fin d => a) (fun _ => b) (low m) - J m| < epsilon / 4 := by
    simpa only [Real.dist_eq] using Metric.tendsto_nhds.mp
      (tendsto_actualPrimeBoxTestSum_cube ha hab (low m) hlow) (epsilon / 4) (by positivity)
  have hNgap : ∀ᶠ N : ℕ in atTop,
      actualPrimeBoxTestSum N (fun _ : Fin d => a) (fun _ => b) (gap m) < E m + epsilon / 4 :=
    (tendsto_actualPrimeBoxTestSum_cube ha hab (gap m) hgap).eventually
      (gt_mem_nhds (by linarith : E m < E m + epsilon / 4))
  filter_upwards [hNlow, hNgap] with N hNl hNg
  have he := actualPrimeBoxTestSum_affineGateRamp_error N
    (fun _ : Fin d => a) (fun _ => b) L c m f
  change |actualPrimeBoxTestSum N (fun _ : Fin d => a) (fun _ => b)
      ((primeAffineGateRegion L c).indicator f) -
      actualPrimeBoxTestSum N (fun _ : Fin d => a) (fun _ => b) (low m)| ≤
    actualPrimeBoxTestSum N (fun _ : Fin d => a) (fun _ => b) (gap m) at he
  rw [Real.dist_eq]
  change |actualPrimeBoxTestSum N (fun _ : Fin d => a) (fun _ => b)
    ((primeAffineGateRegion L c).indicator f) - I| < epsilon
  have htri := (abs_sub_le
    (actualPrimeBoxTestSum N (fun _ : Fin d => a) (fun _ => b)
      ((primeAffineGateRegion L c).indicator f))
    (actualPrimeBoxTestSum N (fun _ : Fin d => a) (fun _ => b) (low m)) I).trans
    (add_le_add le_rfl (abs_sub_le _ (J m) I))
  linarith

end

end ImbalancedChen
