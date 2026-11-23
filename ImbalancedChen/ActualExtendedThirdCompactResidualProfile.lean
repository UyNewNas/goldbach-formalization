import ImbalancedChen.ActualExtendedThirdDistinctPrimeHarmonic
import ImbalancedChen.ActualPrimeBoxOwnCubeResidual

/-!
# Actual lower-density residuals on the original compact cells

The arithmetic summands below are the literal lower Rosser densities,
including their strict own-cube gates.  Their cap is N.  A larger cap
is used only inside an existing uniform approximation theorem, then
removed by a proved equality of the original densities on every actual
selected prime.  The same original cutoff and endpoint conventions stay.

The resulting density sum has the same harmonic profile and retained
cell integral.  This is not yet the signed first-exit coefficient identity
or the counting-error estimate needed for the full arithmetic theorem.
-/

namespace ImbalancedChen

noncomputable section

open Set Filter Topology
open MathlibNt.SieveTheory
open scoped Classical BigOperators

/-- Covering the same actual sifting cutoff makes the literal lower
density independent of its finite ambient prime cap. -/
theorem actualPrimeTupleOwnCubeMinus_cap_congr {k N cap₁ cap₂ : ℕ}
    (hEven : Even N) (p : Fin (k + 1) → ℕ) (lam : ℝ)
    (hc₁ : (p (Fin.last k) : ℝ) ≤ cap₁)
    (hc₂ : (p (Fin.last k) : ℝ) ≤ cap₂) :
    actualPrimeTupleOwnCubeMinus N cap₁ lam p =
      actualPrimeTupleOwnCubeMinus N cap₂ lam p := by
  unfold actualPrimeTupleOwnCubeMinus
  split_ifs
  · rw [actualSmallRosserMinusDensity_eq_b8_mainSum_natCeil N cap₁ hEven _ _ hc₁,
      actualSmallRosserMinusDensity_eq_b8_mainSum_natCeil N cap₂ hEven _ _ hc₂]
  · rfl

/-- The normalization is exactly the manuscript's extended lower factor. -/
theorem primeTupleMinusProfile_eq_extendedThirdFactor (lam : ℝ) (t : Fin 3 → ℝ)
    (hz : 0 < t 2) :
    primeTupleMinusProfile lam t =
      4 * actualExtendedThirdLowerFactor ((lam - t 0 - t 1 - t 2) / t 2) / t 2 := by
  have hsum : lam - ∑ i : Fin 3, t i = lam - t 0 - t 1 - t 2 := by
    rw [Fin.sum_univ_three]
    ring
  unfold primeTupleMinusProfile actualExtendedThirdLowerFactor thirdTailLowerFactor
  rw [hsum, Real.exp_neg]
  change (2 * (Real.exp Real.eulerMascheroniConstant)⁻¹ / t 2) *
      suzukiContinuousLowerFactor (max 2 ((lam - t 0 - t 1 - t 2) / t 2)) = _
  field_simp [ne_of_gt hz, ne_of_gt (Real.exp_pos Real.eulerMascheroniConstant)]
  <;> ring

/-- The limiting extension is zero whenever the original strict gate
fails, including equality.  No arithmetic wall is deleted. -/
theorem primeTupleMinusProfile_ownCube_gate (lam : ℝ) (t : Fin 3 → ℝ)
    (hz : 0 < t 2) :
    (if primeTupleOwnCubeForm t < lam then primeTupleMinusProfile lam t else 0) =
      primeTupleMinusProfile lam t := by
  split_ifs with hg
  · rfl
  · have hg' : lam ≤ t 0 + t 1 + t 2 + 2 * t 2 := by
      have hle : lam ≤ (∑ i : Fin 3, t i) + 2 * t 2 := le_of_not_gt hg
      simpa only [Fin.sum_univ_three] using hle
    have hratio : (lam - t 0 - t 1 - t 2) / t 2 ≤ 2 :=
      (div_le_iff₀ hz).mpr (by linarith only [hg'])
    rw [primeTupleMinusProfile_eq_extendedThirdFactor lam t hz,
      actualExtendedThirdLowerFactor_of_le_two hratio, mul_zero, zero_div]

theorem primeTupleMinusProfile_sub_eq_compactHarmonicProfile {h : ℝ} (hh : 0 < h)
    (e lam : ℝ) (t : Fin 3 → ℝ) (hz : h ≤ t 2) :
    primeTupleMinusProfile (thirdPrefixTheta - 2 * e) t - primeTupleMinusProfile lam t =
      actualExtendedThirdCompactHarmonicProfile e h lam t := by
  rw [primeTupleMinusProfile_eq_extendedThirdFactor _ _ (hh.trans_le hz),
    primeTupleMinusProfile_eq_extendedThirdFactor _ _ (hh.trans_le hz)]
  unfold actualExtendedThirdCompactHarmonicProfile
  rw [max_eq_right (by linarith : h / 2 ≤ t 2)]
  ring

/-- The enlarged cap used by the uniform theorem equals the original
cap N on every selected atom.  In particular N is not silently changed. -/
theorem actualExtendedThirdOwnCubeMinusSum_cap_eq {N : ℕ} (hN : 1 < N)
    (hEven : Even N) (h : ℝ) (m : ℕ) (j : ActualExtendedThirdDyadicLabel m) (lam : ℝ) :
    actualPrimeBoxOwnCubeMinusSum 2 N N (h / 2) (thirdPrefixRho + 1) lam
        (actualExtendedThirdDistinctCellPrimeRegion m j) =
      actualPrimeBoxOwnCubeMinusSum 2 N (Nat.ceil ((N : ℝ) ^ (thirdPrefixRho + 1)))
        (h / 2) (thirdPrefixRho + 1) lam (actualExtendedThirdDistinctCellPrimeRegion m j) := by
  have hNr : (1 : ℝ) < N := by exact_mod_cast hN
  unfold actualPrimeBoxOwnCubeMinusSum
  apply Finset.sum_congr rfl
  intro p hp
  by_cases hr : actualPrimeTupleLog N p ∈ actualExtendedThirdDistinctCellPrimeRegion m j
  · simp only [if_pos hr]
    have hpos (i : Fin 3) : 0 < p i := (mem_actualPrimeBoxTuples_iff.mp hp i).1.pos
    have hlog : actualPrimeTupleLog N p 2 ≤ thirdPrefixRho := hr.1.2.2.1
    have hcN : (p 2 : ℝ) ≤ N := by
      calc
        _ = (N : ℝ) ^ actualPrimeTupleLog N p 2 := (actualPrimeTupleLog_rpow hN p hpos 2).symm
        _ ≤ (N : ℝ) ^ thirdPrefixRho := Real.rpow_le_rpow_of_exponent_le hNr.le hlog
        _ ≤ (N : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hNr.le
          (by norm_num [thirdPrefixRho])
        _ = _ := Real.rpow_one _
    have hcBig : (p 2 : ℝ) ≤ Nat.ceil ((N : ℝ) ^ (thirdPrefixRho + 1)) :=
      (mem_actualPrimeBoxTuples_iff.mp hp 2).2.2.2.le.trans (Nat.le_ceil _)
    exact congrArg (fun r : ℝ => (∏ i : Fin 3, 1 / ((p i : ℝ) - 1)) * r)
      (actualPrimeTupleOwnCubeMinus_cap_congr hEven p lam hcN hcBig)
  · simp only [if_neg hr]

theorem tendsto_actualExtendedThirdOwnCubeMinusSum_error {h : ℝ} {m : ℕ}
    (hh : 0 < h) (hab : h / 2 < thirdPrefixRho + 1)
    (j : ActualExtendedThirdDyadicLabel m) (lam : ℝ) :
    Tendsto (fun N : ℕ =>
      actualPrimeBoxOwnCubeMinusSum 2 N N (h / 2) (thirdPrefixRho + 1) lam
        (actualExtendedThirdDistinctCellPrimeRegion m j) -
      actualPrimeBoxTestSum N (fun _ : Fin 3 => h / 2) (fun _ => thirdPrefixRho + 1)
        (fun t => if t ∈ actualExtendedThirdDistinctCellPrimeRegion m j then
          (if primeTupleOwnCubeForm t < lam then primeTupleMinusProfile lam t else 0) else 0))
      (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N}) (𝓝 0) := by
  let cap : ℕ → ℕ := fun N => Nat.ceil ((N : ℝ) ^ (thirdPrefixRho + 1))
  have hc : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      (N : ℝ) ^ (thirdPrefixRho + 1) ≤ (cap N : ℝ) :=
    Filter.Eventually.of_forall (fun N => Nat.le_ceil _)
  have hlim := tendsto_actualPrimeBoxOwnCubeMinus_error 2 (h / 2) (thirdPrefixRho + 1) lam
    (half_pos hh) hab (actualExtendedThirdDistinctCellPrimeRegion m j) cap hc
  apply hlim.congr'
  have hlarge : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N}, 1 < N :=
    (eventually_gt_atTop 1).filter_mono inf_le_left
  have hEven : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      0 < N ∧ Even N := Filter.Eventually.filter_mono inf_le_right (by simp)
  filter_upwards [hlarge, hEven] with N hN hE
  rw [actualExtendedThirdOwnCubeMinusSum_cap_eq hN hE.2 h m j lam]

def actualExtendedThirdCellResidualDensitySum (N : ℕ) (e h : ℝ) (m : ℕ)
    (j : ActualExtendedThirdDyadicLabel m) : ℝ :=
  actualPrimeBoxOwnCubeMinusSum 2 N N (h / 2) (thirdPrefixRho + 1)
      (thirdPrefixTheta - 2 * e) (actualExtendedThirdDistinctCellPrimeRegion m j) -
    actualPrimeBoxOwnCubeMinusSum 2 N N (h / 2) (thirdPrefixRho + 1)
      (actualExtendedThirdPhysicalLevel e m j) (actualExtendedThirdDistinctCellPrimeRegion m j)

theorem actualExtendedThird_gated_profile_difference {e h : ℝ} {m : ℕ}
    (hh : 0 < h) {j : ActualExtendedThirdDyadicLabel m}
    (hj : j ∈ actualExtendedThirdCompactCells e h m) (N : ℕ) :
    actualPrimeBoxTestSum N (fun _ : Fin 3 => h / 2) (fun _ => thirdPrefixRho + 1)
        (fun t => if t ∈ actualExtendedThirdDistinctCellPrimeRegion m j then
          (if primeTupleOwnCubeForm t < thirdPrefixTheta - 2 * e then
            primeTupleMinusProfile (thirdPrefixTheta - 2 * e) t else 0) else 0) -
      actualPrimeBoxTestSum N (fun _ : Fin 3 => h / 2) (fun _ => thirdPrefixRho + 1)
        (fun t => if t ∈ actualExtendedThirdDistinctCellPrimeRegion m j then
          (if primeTupleOwnCubeForm t < actualExtendedThirdPhysicalLevel e m j then
            primeTupleMinusProfile (actualExtendedThirdPhysicalLevel e m j) t else 0) else 0) =
      actualExtendedThirdDistinctCellPrimeSum N e h m j := by
  unfold actualExtendedThirdDistinctCellPrimeSum actualPrimeBoxTestSum
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro p _
  by_cases hr : actualPrimeTupleLog N p ∈ actualExtendedThirdDistinctCellPrimeRegion m j
  · have hz : h ≤ actualPrimeTupleLog N p 2 :=
      (Finset.mem_filter.mp hj).2.trans (hr.1.1.1 2 (mem_univ _)).1
    simp only [if_pos hr, Set.indicator_of_mem hr]
    rw [primeTupleMinusProfile_ownCube_gate _ _ (hh.trans_le hz),
      primeTupleMinusProfile_ownCube_gate _ _ (hh.trans_le hz), ← mul_sub,
      primeTupleMinusProfile_sub_eq_compactHarmonicProfile hh e
        (actualExtendedThirdPhysicalLevel e m j) _ hz]
  · simp only [if_neg hr, Set.indicator_of_notMem hr, mul_zero, sub_self]

/-- Both real arithmetic lower densities, with their original cap and
strict gates, yield the retained-cell integral without an analytic supplier. -/
theorem tendsto_actualExtendedThirdCellResidualDensitySum {e h : ℝ} {m : ℕ}
    (hh : 0 < h) {j : ActualExtendedThirdDyadicLabel m}
    (hj : j ∈ actualExtendedThirdCompactCells e h m) :
    Tendsto (fun N : ℕ => actualExtendedThirdCellResidualDensitySum N e h m j)
      (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N})
      (𝓝 (actualExtendedThirdRetainedCellIntegral e m j)) := by
  have hhrho : h ≤ thirdPrefixRho :=
    (Finset.mem_filter.mp hj).2.trans
      ((actualExtendedThirdDyadic_bounds m j 2).2.1.le.trans
        (actualExtendedThirdDyadic_bounds m j 2).2.2)
  have hab : h / 2 < thirdPrefixRho + 1 := by linarith
  have hOld := tendsto_actualExtendedThirdOwnCubeMinusSum_error hh hab j (thirdPrefixTheta - 2 * e)
  have hCell := tendsto_actualExtendedThirdOwnCubeMinusSum_error hh hab j
    (actualExtendedThirdPhysicalLevel e m j)
  have hPrime := (tendsto_actualExtendedThirdDistinctCellPrimeSum hh hj).mono_left
    (show atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N} ≤ atTop from inf_le_left)
  have hlim := (hOld.sub hCell).add hPrime
  simp only [sub_self, zero_add] at hlim
  convert hlim using 1
  funext N
  rw [← actualExtendedThird_gated_profile_difference hh hj N]
  unfold actualExtendedThirdCellResidualDensitySum
  ring

def actualExtendedThirdCompactResidualDensitySum (N : ℕ) (e h : ℝ) (m : ℕ) : ℝ :=
  ∑ j ∈ actualExtendedThirdCompactCells e h m,
    actualExtendedThirdCellResidualDensitySum N e h m j

theorem tendsto_actualExtendedThirdCompactResidualDensitySum {e h : ℝ}
    (hh : 0 < h) (he0 : 0 ≤ e) (he : e ≤ 1 / 384) (m : ℕ) :
    Tendsto (fun N : ℕ => actualExtendedThirdCompactResidualDensitySum N e h m)
      (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N})
      (𝓝 (actualExtendedThirdCompactCellFunctional e h m)) := by
  rw [actualExtendedThirdCompactCellFunctional_eq_sum_cells he0 he m]
  exact tendsto_finsetSum _ (fun _j hj => tendsto_actualExtendedThirdCellResidualDensitySum hh hj)

theorem exists_actualExtendedThirdCompactResidualDensitySum_approx_ideal
    {ε : ℝ} (hε : 0 < ε) :
    ∃ h : ℝ, 0 < h ∧ ∃ e : ℝ, 0 < e ∧ e ≤ 1 / 384 ∧ ∃ m : ℕ,
      ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
        |actualExtendedThirdCompactResidualDensitySum N e h m -
          actualExtendedThirdIdealFunctional| ≤ ε := by
  obtain ⟨h, hh, e₀, he₀, he₀cap, m₀, hb⟩ :=
    actualExtendedThirdCompactCellFunctional_uniform_approx (half_pos hε)
  have hepos : 0 < e₀ / 2 := half_pos he₀
  have hecap : e₀ / 2 ≤ 1 / 384 := (by linarith : e₀ / 2 ≤ e₀).trans he₀cap
  have hcont : |actualExtendedThirdCompactCellFunctional (e₀ / 2) h m₀ -
      actualExtendedThirdIdealFunctional| ≤ ε / 2 :=
    hb (e₀ / 2) hepos.le (by linarith) m₀ le_rfl
  have hArith : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      |actualExtendedThirdCompactResidualDensitySum N (e₀ / 2) h m₀ -
        actualExtendedThirdCompactCellFunctional (e₀ / 2) h m₀| < ε / 2 := by
    simpa only [Real.dist_eq] using Metric.tendsto_nhds.mp
      (tendsto_actualExtendedThirdCompactResidualDensitySum hh hepos.le hecap m₀)
        (ε / 2) (half_pos hε)
  refine ⟨h, hh, e₀ / 2, hepos, hecap, m₀, ?_⟩
  filter_upwards [hArith] with N hN
  apply (abs_sub_le _ (actualExtendedThirdCompactCellFunctional (e₀ / 2) h m₀) _).trans
  exact (add_le_add hN.le hcont).trans (by linarith)

end

end ImbalancedChen
