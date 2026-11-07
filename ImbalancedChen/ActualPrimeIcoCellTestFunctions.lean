import ImbalancedChen.ActualPrimePolyhedralTestFunctions
import ImbalancedChen.LogPrimeBoxMesh

/-!
# Actual prime tests on half-open mesh cells

Continuous ramps sandwich a region between its strict and weak affine
gates. The sandwich controls the actual prime atoms even on the walls.
Only the continuous integral uses the proved null-wall identity. Thus the
Ico ownership of every mesh face is retained in the arithmetic sum.
-/

namespace ImbalancedChen

noncomputable section

open scoped Classical BigOperators Topology
open MeasureTheory Filter Set

private theorem affinePrimeGateRamp_upper_eq_one_of_le {d r : ℕ}
    (L : Fin r → (Fin d → ℝ) →L[ℝ] ℝ) (c : Fin r → ℝ) (m : ℕ)
    {x : Fin d → ℝ} (hx : ∀ j, L j x ≤ c j) :
    affinePrimeGateRamp L c true m x = 1 := by
  apply Finset.prod_eq_one
  intro j _
  apply affinePrimeClamp_eq_one
  simp only [if_true]
  have hp : 0 ≤ (m + 1 : ℝ) * (c j - L j x) :=
    mul_nonneg (by positivity) (sub_nonneg.mpr (hx j))
  linarith

private theorem affineSandwich_test_error {d r : ℕ}
    (L : Fin r → (Fin d → ℝ) →L[ℝ] ℝ) (c : Fin r → ℝ)
    (R : Set (Fin d → ℝ)) (hlo : primeAffineGateRegion L c ⊆ R)
    (hhi : ∀ x ∈ R, ∀ j, L j x ≤ c j) (m : ℕ)
    (f : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) :
    |R.indicator f x - f x * affinePrimeGateRamp L c false m x| ≤
      |f x| * (affinePrimeGateRamp L c true m x - affinePrimeGateRamp L c false m x) := by
  by_cases hx : x ∈ R
  · rw [indicator_of_mem hx, affinePrimeGateRamp_upper_eq_one_of_le L c m (hhi x hx)]
    rw [show f x - f x * affinePrimeGateRamp L c false m x =
      f x * (1 - affinePrimeGateRamp L c false m x) by ring, abs_mul,
      abs_of_nonneg (sub_nonneg.mpr (affinePrimeGateRamp_bounds L c false m x).2)]
  · rw [indicator_of_notMem hx,
      affinePrimeGateRamp_lower_eq_zero L c m (fun hg => hx (hlo hg))]
    simp only [mul_zero, sub_zero, abs_zero]
    exact mul_nonneg (abs_nonneg _) (affinePrimeGateRamp_bounds L c true m x).1

private theorem integral_affineSandwich {d r : ℕ} (a b : ℝ)
    (L : Fin r → (Fin d → ℝ) →L[ℝ] ℝ) (c : Fin r → ℝ) (hL : ∀ j, L j ≠ 0)
    (R : Set (Fin d → ℝ)) (hR : MeasurableSet R)
    (hlo : primeAffineGateRegion L c ⊆ R) (hhi : ∀ x ∈ R, ∀ j, L j x ≤ c j)
    (f : (Fin d → ℝ) → ℝ) :
    (∫ x in logPrimeBox (fun _ : Fin d => a) (fun _ => b) ∩ primeAffineGateRegion L c,
      f x * ∏ i, 1 / x i) =
    ∫ x in logPrimeBox (fun _ : Fin d => a) (fun _ => b) ∩ R,
      f x * ∏ i, 1 / x i := by
  rw [← setIntegral_indicator (measurableSet_primeAffineGateRegion L c),
    ← setIntegral_indicator hR]
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae (ae_primeAffineGate_no_wall L c hL)] with x hx
  have hiff : x ∈ primeAffineGateRegion L c ↔ x ∈ R :=
    ⟨fun hg => hlo hg, fun hr j => lt_of_le_of_ne (hhi x hr j) (hx j)⟩
  by_cases hr : x ∈ R
  · simp only [indicator_of_mem hr, indicator_of_mem (hiff.mpr hr)]
  · simp only [indicator_of_notMem hr, indicator_of_notMem (mt hiff.mp hr)]

/-- Mixed strict and weak affine gates have the true prime integral limit.
The arithmetic sandwich, including wall atoms, is proved pointwise; no
null-wall or arithmetic limit premise is required from the caller. -/
theorem tendsto_actualPrimeBoxTestSum_cube_affineSandwich {d r : ℕ} {a b : ℝ}
    (ha : 0 < a) (hab : a < b)
    (L : Fin r → (Fin d → ℝ) →L[ℝ] ℝ) (c : Fin r → ℝ) (hL : ∀ j, L j ≠ 0)
    (R : Set (Fin d → ℝ)) (hR : MeasurableSet R)
    (hlo : primeAffineGateRegion L c ⊆ R) (hhi : ∀ x ∈ R, ∀ j, L j x ≤ c j)
    (f : (Fin d → ℝ) → ℝ)
    (hf : ContinuousOn f (Set.univ.pi (fun _ : Fin d => Set.Icc a b))) :
    Tendsto (fun N : ℕ => actualPrimeBoxTestSum N (fun _ : Fin d => a) (fun _ => b)
      (R.indicator f)) atTop
      (𝓝 (∫ x in logPrimeBox (fun _ : Fin d => a) (fun _ => b) ∩ R,
        f x * ∏ i, 1 / x i)) := by
  rw [← integral_affineSandwich a b L c hL R hR hlo hhi f, Metric.tendsto_nhds]
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
  have he : |actualPrimeBoxTestSum N (fun _ : Fin d => a) (fun _ => b) (R.indicator f) -
      actualPrimeBoxTestSum N (fun _ : Fin d => a) (fun _ => b) (low m)| ≤
      actualPrimeBoxTestSum N (fun _ : Fin d => a) (fun _ => b) (gap m) := by
    unfold actualPrimeBoxTestSum
    rw [← Finset.sum_sub_distrib]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro p hp
    rw [← mul_sub, abs_mul, abs_of_nonneg (actualPrimeBoxWeight_nonneg hp)]
    exact mul_le_mul_of_nonneg_left (affineSandwich_test_error L c R hlo hhi m f _)
      (actualPrimeBoxWeight_nonneg hp)
  rw [Real.dist_eq]
  change |actualPrimeBoxTestSum N (fun _ : Fin d => a) (fun _ => b) (R.indicator f) - I| < epsilon
  have htri := (abs_sub_le
    (actualPrimeBoxTestSum N (fun _ : Fin d => a) (fun _ => b) (R.indicator f))
    (actualPrimeBoxTestSum N (fun _ : Fin d => a) (fun _ => b) (low m)) I).trans
    (add_le_add le_rfl (abs_sub_le _ (J m) I))
  linarith

/-- Lower coordinate rows, upper coordinate rows, and the caller's rows. -/
def primeIcoBoxGateForms {d r : ℕ}
    (L : Fin r → (Fin d → ℝ) →L[ℝ] ℝ) :
    Fin (d + (d + r)) → (Fin d → ℝ) →L[ℝ] ℝ :=
  Fin.append (fun i => -ContinuousLinearMap.proj i)
    (Fin.append (fun i => ContinuousLinearMap.proj i) L)

def primeIcoBoxGateBounds {d r : ℕ} (lo hi : Fin d → ℝ) (c : Fin r → ℝ) :
    Fin (d + (d + r)) → ℝ :=
  Fin.append (fun i => -lo i) (Fin.append hi c)

theorem primeIcoBoxGateForms_ne_zero {d r : ℕ}
    (L : Fin r → (Fin d → ℝ) →L[ℝ] ℝ) (hL : ∀ j, L j ≠ 0) :
    ∀ j, primeIcoBoxGateForms L j ≠ 0 := by
  have hp (i : Fin d) : (ContinuousLinearMap.proj i : (Fin d → ℝ) →L[ℝ] ℝ) ≠ 0 := by
    intro h
    have hh := congrArg (fun F : (Fin d → ℝ) →L[ℝ] ℝ => F (fun _ => 1)) h
    simp at hh
  simp only [primeIcoBoxGateForms, Fin.forall_fin_add, Fin.append_left, Fin.append_right]
  exact ⟨fun i => neg_ne_zero.mpr (hp i), hp, hL⟩

theorem mem_primeIcoBoxStrictGateRegion {d r : ℕ}
    (lo hi : Fin d → ℝ) (L : Fin r → (Fin d → ℝ) →L[ℝ] ℝ) (c : Fin r → ℝ)
    (x : Fin d → ℝ) :
    x ∈ primeAffineGateRegion (primeIcoBoxGateForms L) (primeIcoBoxGateBounds lo hi c) ↔
      (∀ i, lo i < x i ∧ x i < hi i) ∧ x ∈ primeAffineGateRegion L c := by
  simp only [primeAffineGateRegion, mem_ofPred_eq, primeIcoBoxGateForms,
    primeIcoBoxGateBounds, Fin.forall_fin_add, Fin.append_left, Fin.append_right,
    neg_apply, ContinuousLinearMap.proj_apply, neg_lt_neg_iff]
  constructor
  · rintro ⟨hl, hu, hg⟩
    exact ⟨fun i => ⟨hl i, hu i⟩, hg⟩
  · rintro ⟨hbox, hg⟩
    exact ⟨fun i => (hbox i).1, fun i => (hbox i).2, hg⟩

private theorem primeIcoBox_weak_gates {d r : ℕ}
    (lo hi : Fin d → ℝ) (L : Fin r → (Fin d → ℝ) →L[ℝ] ℝ) (c : Fin r → ℝ)
    {x : Fin d → ℝ} (hx : x ∈ logPrimeBox lo hi ∩ primeAffineGateRegion L c) :
    ∀ j, primeIcoBoxGateForms L j x ≤ primeIcoBoxGateBounds lo hi c j := by
  simp only [primeIcoBoxGateForms, primeIcoBoxGateBounds, Fin.forall_fin_add,
    Fin.append_left, Fin.append_right, neg_apply,
    ContinuousLinearMap.proj_apply, neg_le_neg_iff]
  exact ⟨fun i => (mem_logPrimeBox.mp hx.1 i).1,
    fun i => (mem_logPrimeBox.mp hx.1 i).2.le, fun j => (hx.2 j).le⟩

/-- The actual signed test sum on one Ico cell and finitely many strict
affine gates converges to its true integral. Dimension zero and an empty
gate family are permitted. The mesh is fixed before N tends to infinity. -/
theorem tendsto_actualPrimeBoxTestSum_cube_IcoCell_affineGates {d r : ℕ} {a b : ℝ}
    (ha : 0 < a) (hab : a < b) (m : ℕ) (j : Fin d → Fin (m + 1))
    (L : Fin r → (Fin d → ℝ) →L[ℝ] ℝ) (c : Fin r → ℝ) (hL : ∀ i, L i ≠ 0)
    (f : (Fin d → ℝ) → ℝ)
    (hf : ContinuousOn f (Set.univ.pi (fun _ : Fin d => Set.Icc a b))) :
    Tendsto (fun N : ℕ => actualPrimeBoxTestSum N (fun _ : Fin d => a) (fun _ => b)
      ((logPrimeMeshCell a b m j ∩ primeAffineGateRegion L c).indicator f)) atTop
      (𝓝 (∫ x in logPrimeMeshCell a b m j ∩ primeAffineGateRegion L c,
        f x * ∏ i, 1 / x i)) := by
  have hlo : primeAffineGateRegion (primeIcoBoxGateForms L)
      (primeIcoBoxGateBounds (logPrimeMeshLo a b m j) (logPrimeMeshHi a b m j) c) ⊆
      logPrimeMeshCell a b m j ∩ primeAffineGateRegion L c := by
    intro x hx
    obtain ⟨hb, hg⟩ := (mem_primeIcoBoxStrictGateRegion _ _ L c x).mp hx
    exact ⟨mem_logPrimeMeshCell.mpr (fun i => ⟨(hb i).1.le, (hb i).2⟩), hg⟩
  have ht := tendsto_actualPrimeBoxTestSum_cube_affineSandwich ha hab
    (primeIcoBoxGateForms L)
    (primeIcoBoxGateBounds (logPrimeMeshLo a b m j) (logPrimeMeshHi a b m j) c)
    (primeIcoBoxGateForms_ne_zero L hL)
    (logPrimeMeshCell a b m j ∩ primeAffineGateRegion L c)
    ((measurableSet_logPrimeMeshCell a b m j).inter (measurableSet_primeAffineGateRegion L c))
    hlo (fun _ hx => primeIcoBox_weak_gates _ _ L c hx) f hf
  have heq : logPrimeBox (fun _ : Fin d => a) (fun _ => b) ∩
      (logPrimeMeshCell a b m j ∩ primeAffineGateRegion L c) =
      logPrimeMeshCell a b m j ∩ primeAffineGateRegion L c :=
    inter_eq_right.mpr (fun _ hx => logPrimeMeshCell_subset_box hab m j hx.1)
  simpa only [heq] using ht

end

end ImbalancedChen
